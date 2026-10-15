-- TNS|ExpressLRS Bind|TNE
---- ##########################################################################
---- #                                                                        #
---- # ExpressLRS bind phrase manager for B&W LCD radios only             #
---- # Designed for broader EdgeTX compatibility, without the original        #
---- # script's EdgeTX 2.11.6+/2.12.1+ requirement. Reads and writes the      #
---- # bind phrase / UID over MSP; the device side requires ExpressLRS 4.1+.  #
---- #                                                                        #
---- # Author: jtshs256@gmail.com                                             #
---- # Co-author: GPT-5.6 Luna                                                #
---- #                                                                        #
---- # Based on the ExpressLRS project source files and licensed under GPLv3. #
---- # License GPLv3: https://www.gnu.org/licenses/gpl-3.0.html               #
---- #                                                                        #
---- ##########################################################################

local TX=0xEE
local RX=0xEC
local HANDSET=0xEA
local COMMAND=0x32
local PARAM_WRITE=0x2D
local ELRS_STATUS=0x2E
local MSP_REQ=0x7A
local MSP_RESP=0x7B
local MSP_WRITE=0x7C
local CMD_RX=0x10
local CMD_BIND=0x01
local MSP_FN=0x2D
local UID_CMD=0x00
local PHRASE_CMD=0x01
local MSP_START=0x10
local MSP_V1=0x20
local MSP_VER_MASK=0x60
local PHRASE_MAX=52
local RETRY=50
local MAX_RETRY=12
local FOLLOW=100
local WRITE_SETTLE=200

local TARGET_TX=1
local TARGET_RX=2
local TARGET_BOTH=3
local target=TARGET_TX
local phrase=""
local uid={0,0,0,0,0,0}
local uidFrom=nil
local status="Ready"
local attempts=0
local timer=nil
local timerAt=0
local timerTicks=0
local uidGuardUntil=0
local elrsStatusSeen=false
local elrsStatusAt=0
local elrsStatusPollAt=0
local ELRS_STATUS_POLL=50
local ELRS_STATUS_TIMEOUT=150
local LINK_UNKNOWN=0
local LINK_DOWN=1
local LINK_UP=2
local LINK_WAIT_DOWN=3
local linkState=LINK_UNKNOWN
local linkCandidate=nil
local linkSamples=0
local bindRefreshRx=false
local uidTimeoutRecovery=false
local LINK_CONFIRM_SAMPLES=2
local uidReadDest=nil
local UID_LATE_RESPONSE_GUARD=RETRY*MAX_RETRY
local selected=1
local exitRequested=false
local edit=nil
local bwRows={}
local rowsTarget=0
local bwFirst=1
local bwLastStatus=nil
local bwStatusAt=0
local BW_STATUS_TICKS=300
-- 128x96 radios such as the TBS Tango 2 can show three more 8px rows than
-- 64px-high displays while keeping the status line clear at the bottom.
local VISIBLE_ROWS=(LCD_H>=96) and 9 or 6
local history={}
local bothRxWriteQueued=nil
local bothPhrase=nil
local historyOpen=false
local historySelected=nil
local historyFirst=nil
local historyConfirm=nil
local forceRedraw=true
local lastStatus=nil
local lastLink=nil

local ROW_PHRASE=1
local ROW_TARGET=2
local ROW_UID=3
local ROW_SET=4
local ROW_LINK=5
local ROW_EXIT=7
local ROW_HISTORY=8
local HISTORY_MAX=5
local HISTORY_PATH="/SCRIPTS/TOOLS/elrs-history.txt"
local HISTORY_LINE_MAX=PHRASE_MAX+8
local HISTORY_READ_LIMIT=HISTORY_MAX*(PHRASE_MAX+12)

local COL2=(LCD_W==212) and 110 or 70
local CHARS=" abcdefghijklmnopqrstuvwxyz0123456789_-,."

-- Reusable protocol buffers reduce temporary table allocation on FreedomTX.
local statusReq={TX,HANDSET,0,0}
local bindTx={TX,HANDSET,CMD_RX,CMD_BIND}
local bindRx={RX,HANDSET,CMD_RX,CMD_BIND}
local out={}

-- ---------------------------------------------------------------------------
-- Standalone bind phrase history. EdgeTX uses io.read/io.write/io.close
-- functions rather than file-object methods.
-- ---------------------------------------------------------------------------
local function historySave()
  local f=io.open(HISTORY_PATH,"w")
  if not f then return false end
  for i=1,#history do io.write(f,"h"..i.."="..history[i].."\n") end
  io.close(f)
  return true
end
local function historyLoad()
  -- Read bounded chunks and store values directly in the existing table.
  for i=#history,1,-1 do history[i]=nil end
  local f=io.open(HISTORY_PATH,"r")
  if not f then return end
  local carry=""
  local bytesRead=0
  local malformed=false
  while bytesRead<HISTORY_READ_LIMIT and not malformed do
    local part=io.read(f,math.min(64,HISTORY_READ_LIMIT-bytesRead))
    if not part or #part==0 then break end
    bytesRead=bytesRead+#part
    local data=part
    if carry~="" then data=carry..part end
    local pos=1
    carry=""
    while true do
      local nl=string.find(data,"\n",pos,true)
      if not nl then
        carry=string.sub(data,pos)
        if #carry>HISTORY_LINE_MAX then malformed=true;carry="" end
        break
      end
      if nl-pos>HISTORY_LINE_MAX then
        malformed=true
        break
      end
      local lineEnd=nl-1
      if lineEnd>=pos and string.byte(data,lineEnd)==13 then lineEnd=lineEnd-1 end
      if lineEnd>=pos and string.byte(data,pos)==104 and string.byte(data,pos+2)==61 then
        local idx=string.byte(data,pos+1)-48
        local valueStart=pos+3
        local valueLen=lineEnd-valueStart+1
        if idx>=1 and idx<=HISTORY_MAX and valueLen>0 and valueLen<=PHRASE_MAX then
          history[idx]=string.sub(data,valueStart,lineEnd)
        end
      end
      pos=nl+1
    end
  end
  io.close(f)
  -- Compact in place so no second history table is allocated.
  local w=1
  for i=1,HISTORY_MAX do
    if history[i] then history[w]=history[i];if w~=i then history[i]=nil end;w=w+1 end
  end
end
local function historyAdd(value)
  if not value or value=="" then return end
  for i=#history,1,-1 do
    if history[i]==value then
      for j=i,#history-1 do history[j]=history[j+1] end
      history[#history]=nil
    end
  end
  for i=math.min(#history+1,HISTORY_MAX),2,-1 do history[i]=history[i-1] end
  history[1]=value
  historySave()
end
local function historyRemove(idx)
  if not history[idx] then return end
  for i=idx,#history-1 do history[i]=history[i+1] end
  history[#history]=nil
  historySave()
end
local function historyClear() for i=#history,1,-1 do history[i]=nil end;historySave() end

-- ---------------------------------------------------------------------------
-- Timer / link helpers
-- ---------------------------------------------------------------------------
local function schedule(t,k) timerAt=getTime();timerTicks=t;timer=k end
local function cancel() timer=nil end
local function abandonUidRequest()
  uidReadDest=nil
  attempts=0
  if timer=="uid" or timer=="autoUid" then cancel() end
end
local function acceptLinkSample(connected)
  local sample=connected and LINK_UP or LINK_DOWN
  -- While requesting an unbind, remember connected samples but do not let a
  -- delayed pre-command status frame immediately restore the link state.
  if linkState==LINK_WAIT_DOWN and sample==LINK_UP then
    if linkCandidate==sample then linkSamples=linkSamples+1
    else linkCandidate=sample;linkSamples=1 end
    return
  end
  if linkCandidate==sample then linkSamples=linkSamples+1
  else linkCandidate=sample;linkSamples=1 end
  if linkSamples>=LINK_CONFIRM_SAMPLES then
    linkState=sample
    linkCandidate=nil
    linkSamples=0
    if sample==LINK_UP and (bindRefreshRx or uidTimeoutRecovery) then
      bindRefreshRx=false
      uidTimeoutRecovery=false
      target=TARGET_RX
      rowsTarget=0
      uidReadDest=nil
      attempts=0
      status="RX linked, reading UID..."
      schedule(WRITE_SETTLE,"readBack")
    end
  end
end
local function requestElrsStatus()
  local now=getTime()
  if elrsStatusSeen and now-elrsStatusAt>=ELRS_STATUS_TIMEOUT then
    linkState=LINK_UNKNOWN
    linkCandidate=nil
    linkSamples=0
  end
  if now-elrsStatusPollAt<ELRS_STATUS_POLL then return end
  -- Continue polling during UID retries so a live RX is not mistaken for a
  -- disconnected one when the UID response times out.
  if (timer~=nil and timer~="uid" and timer~="autoUid" and timer~="readBack")
      or (attempts>0 and timer~="uid" and timer~="readBack") then return end
  crossfireTelemetryPush(PARAM_WRITE,statusReq)
  elrsStatusPollAt=now
end

local function isNextEvent(event)
  return event==EVT_VIRTUAL_NEXT
      or event==EVT_VIRTUAL_NEXT_REPT
      or event==EVT_ROT_RIGHT
      or event==EVT_ROT_RIGHT_REPT
      or event==EVT_PLUS_FIRST
      or event==EVT_PLUS_REPT
end

local function isPrevEvent(event)
  return event==EVT_VIRTUAL_PREV
      or event==EVT_VIRTUAL_PREV_REPT
      or event==EVT_ROT_LEFT
      or event==EVT_ROT_LEFT_REPT
      or event==EVT_MINUS_FIRST
      or event==EVT_MINUS_REPT
end

-- ---------------------------------------------------------------------------
-- MSP-over-CRSF, exact single-frame format used by current ELRS Lua.
-- ---------------------------------------------------------------------------
local function pushMsp(frame,dest,cmd,text)
  out[1]=dest;out[2]=HANDSET;out[3]=MSP_V1+MSP_START;out[5]=MSP_FN;out[6]=cmd
  local n=1
  if text then
    n=#text+1
    for i=1,#text do out[6+i]=string.byte(text,i) end
  end
  out[4]=n
  for i=#out,6+n,-1 do out[i]=nil end
  return crossfireTelemetryPush(frame,out)
end
local function writeUid(dest,u)
  for i=#out,13,-1 do out[i]=nil end
  out[1]=dest;out[2]=HANDSET;out[3]=MSP_V1+MSP_START;out[4]=7;out[5]=MSP_FN;out[6]=UID_CMD
  for i=1,6 do out[6+i]=u[i] end
  return crossfireTelemetryPush(MSP_WRITE,out)
end
-- ---------------------------------------------------------------------------
-- MSP UID response decoder, copied in behavior from msp.decodeUid().
-- ---------------------------------------------------------------------------
local function decodeUid(d)
  if not d or d[1]~=HANDSET then return nil end
  local st,size,fn=d[3],d[4],d[5]
  if not st or not size or not fn then return nil end
  if bit32.band(st,MSP_START)==0 then return nil end
  if bit32.band(st,MSP_VER_MASK)~=MSP_V1 then return nil end
  if fn~=MSP_FN or size<7 or d[6]~=UID_CMD then return nil end
  if d[5+size]==nil then return nil end
  for i=1,6 do if d[6+i]==nil then return nil end end
  return d[2]
end
local function drain()
  while true do
    local c,d=crossfireTelemetryPop()
    if not c then break end
    if c==ELRS_STATUS and d and d[2]==TX and d[6]~=nil then
      -- Exact crsf.lua decode: ELRS_STATUS flags byte bit 0 is RX connected.
      elrsStatusSeen=true
      elrsStatusAt=getTime()
      acceptLinkSample(bit32.btest(d[6],1))
    end

    if c==MSP_RESP then
      local src=decodeUid(d)
      if src and (src==TX or src==RX) and uidReadDest and attempts>0 and timer=="uid" and uidGuardUntil>getTime() then
        for i=1,6 do uid[i]=d[6+i] end
        uidFrom=uidReadDest
        uidTimeoutRecovery=false
        status=nil
        attempts=0
        uidReadDest=nil
        uidGuardUntil=0
        if timer=="uid" then cancel() end
        elrsStatusPollAt=getTime()-ELRS_STATUS_POLL
        collectgarbage()
      end
    end
  end
end

-- ---------------------------------------------------------------------------
-- UID text parsing. A comma-separated 4..6 byte string is treated as raw UID.
-- ---------------------------------------------------------------------------
local function parseByte(s,i,j)
  while i<=j and string.byte(s,i)==32 do i=i+1 end
  while j>=i and string.byte(s,j)==32 do j=j-1 end
  if i>j or j-i>2 then return nil end
  local n=0
  for k=i,j do
    local b=string.byte(s,k)
    if b<48 or b>57 then return nil end
    n=n*10+b-48
  end
  return n<=255 and n or nil
end
local function parseUidText(s)
  -- Parse ranges in place; do not allocate one substring per UID byte.
  local count,pos=0,1
  for i=1,6 do uid[i]=0 end
  while pos<=#s do
    local q=string.find(s,",",pos,true)
    local last=q and q-1 or #s
    if q==#s then return nil end
    local n=parseByte(s,pos,last)
    if not n or count>=6 then return nil end
    count=count+1
    uid[count]=n
    if not q then break end
    pos=q+1
  end
  if count<4 then return nil end
  if count<6 then
    for i=count,1,-1 do uid[6-count+i]=uid[i] end
    for i=1,6-count do uid[i]=0 end
  end
  return uid
end
-- ---------------------------------------------------------------------------
-- B&W text editor from current ELRS text_edit.lua.
-- ---------------------------------------------------------------------------
local function charIndex(c)
  local b=string.byte(c)
  if b and b>=65 and b<=90 then c=string.char(b+32) end
  return string.find(CHARS,c,1,true) or 1
end
local function editorSet(e,c)
  local v=e.value
  if #v<e.cur-1 then v=v..string.rep(" ",e.cur-1-#v) end
  e.value=string.sub(v,1,e.cur-1)..c..string.sub(v,e.cur+1)
end
local function editorEvent(e,event)
  local c=string.sub(e.value,e.cur,e.cur);if c=="" then c=" " end
  -- Accept both the virtual field-navigation events used by EdgeTX and
  -- the physical +/- / rotary events that some color radios expose.
  local nextChar=isNextEvent(event)
  local prevChar=isPrevEvent(event)
  if nextChar or prevChar then
    local n=charIndex(c)
    if nextChar then
      n=n+1
      if n>#CHARS then n=1 end
    else
      n=n-1
      if n<1 then n=#CHARS end
    end
    local nc=string.sub(CHARS,n,n)
    local cb,nb=string.byte(c),string.byte(nc)
    if cb and cb>=65 and cb<=90 and nb and nb>=97 and nb<=122 then nc=string.char(nb-32) end
    editorSet(e,nc);return false
  end
  if event==EVT_VIRTUAL_ENTER then
    if e.cur<e.maxLen then
      e.cur=e.cur+1
      if e.cur>=e.first+e.visible then e.first=e.cur-e.visible+1 end
      return false
    end
    e.editing=false;local z=#e.value;while z>0 and string.byte(e.value,z)==32 do z=z-1 end;e.value=string.sub(e.value,1,z);return true
  end
  if event==EVT_VIRTUAL_ENTER_LONG then
    killEvents(event)
    if c==" " then e.editing=false;local z=#e.value;while z>0 and string.byte(e.value,z)==32 do z=z-1 end;e.value=string.sub(e.value,1,z);return true end
    local b=string.byte(c)
    if b and b>=65 and b<=90 then editorSet(e,string.char(b+32))
    elseif b and b>=97 and b<=122 then editorSet(e,string.char(b-32)) end
    return false
  end
  if event==EVT_VIRTUAL_EXIT then e.editing=false;local z=#e.value;while z>0 and string.byte(e.value,z)==32 do z=z-1 end;e.value=string.sub(e.value,1,z);return true end
  return false
end
local function editorDraw(e,x,y,attr)
  local visible=e.visible
  if not e.editing then
    local text=e.value
    if text=="" then text="---" end
    lcd.drawText(x,y,string.sub(text,1,visible),attr)
    return
  end
  -- Keep the phrase in its native B&W text positions. Then place the cursor
  -- at the exact right edge reported after drawing the visible prefix. This
  -- avoids changing character spacing and avoids cumulative fixed-width error.
  if e.cur<e.first then e.first=e.cur end
  if e.cur>=e.first+visible then e.first=e.cur-visible+1 end
  local last=e.first+visible-1
  local shown=string.sub(e.value,e.first,last)
  lcd.drawText(x,y,shown,0)
  local prefix=string.sub(e.value,e.first,e.cur-1)
  local px=x
  if prefix~="" then
    lcd.drawText(x,y,prefix,0)
    if lcd.getLastRightPos then px=lcd.getLastRightPos() else px=x+#prefix*6 end
  end
  local c=string.sub(e.value,e.cur,e.cur)
  if c=="" then c=" " end
  lcd.drawText(px,y,c,INVERS)
end
local phraseEditor={maxLen=PHRASE_MAX,visible=math.floor((LCD_W-COL2-2)/6),value="",cur=1,first=1,editing=false}

-- ---------------------------------------------------------------------------
-- Operations.
-- ---------------------------------------------------------------------------
local startUidRead


local function changeTarget(newTarget)
  if newTarget<TARGET_TX then
    newTarget=TARGET_BOTH
  elseif newTarget>TARGET_BOTH then
    newTarget=TARGET_TX
  end

  if timer=="bothTX" or timer=="unbindDone" then status="Finish current operation first";return end
  abandonUidRequest()
  target=newTarget
  bindRefreshRx=false
  uidTimeoutRecovery=false
  uid[1]=0;uid[2]=0;uid[3]=0;uid[4]=0;uid[5]=0;uid[6]=0;uidFrom=nil
  cancel()

  if target==TARGET_TX or target==TARGET_RX then
    startUidRead()
  else
    status="Target: Both"
  end
end

startUidRead=function()
  if timer=="bothTX" or timer=="unbindDone" then status="Finish current operation first";return end
  if target==TARGET_BOTH then
    uid[1]=0;uid[2]=0;uid[3]=0;uid[4]=0;uid[5]=0;uid[6]=0;uidFrom=nil
    status="Target: Both"
    cancel()
    return
  end

  if timer=="uid" and attempts>0 then abandonUidRequest() end

  if target==TARGET_RX and linkState~=LINK_UP then
    uid[1]=0;uid[2]=0;uid[3]=0;uid[4]=0;uid[5]=0;uid[6]=0;uidFrom=nil
    uidReadDest=nil
    attempts=0
    uidTimeoutRecovery=true
    cancel()
    status="RX link not active"
    return
  end

  local now=getTime()
  if now<uidGuardUntil then
    schedule(uidGuardUntil-now,"autoUid")
    status="Waiting for previous UID reply..."
    return
  end
  uidGuardUntil=0

  uidReadDest=(target==TARGET_RX) and RX or TX
  uid[1]=0;uid[2]=0;uid[3]=0;uid[4]=0;uid[5]=0;uid[6]=0;uidFrom=nil
  attempts=1
  status="Reading "..((target==TARGET_RX) and "RX" or "TX").." UID..."
  elrsStatusPollAt=getTime()
  if pushMsp(MSP_REQ,uidReadDest,UID_CMD) then uidGuardUntil=getTime()+UID_LATE_RESPONSE_GUARD
  else status="Telemetry busy" end
  schedule(RETRY,"uid")
end
local function retryUid()
  if attempts>=MAX_RETRY then
    status=(uidGuardUntil>0) and "No response" or "Telemetry busy"
    attempts=0
    cancel()
    uidReadDest=nil
    if target==TARGET_RX and linkState~=LINK_UP then uidTimeoutRecovery=true end
    elrsStatusPollAt=getTime()-ELRS_STATUS_POLL
    collectgarbage()
    return
  end
  if not uidReadDest then
    cancel()
    return
  end
  if pushMsp(MSP_REQ,uidReadDest,UID_CMD) then
    uidGuardUntil=getTime()+UID_LATE_RESPONSE_GUARD
    status="Reading "..((target==TARGET_RX) and "RX" or "TX").." UID..."
  elseif uidGuardUntil==0 then
    status="Telemetry busy"
  end
  attempts=attempts+1
  schedule(RETRY,"uid")
end
local function setOne(which,value)
  local dest=(which==TARGET_TX) and TX or RX
  if value==nil then value=phrase end
  local u=parseUidText(value)
  if u then
    for i=1,6 do uid[i]=u[i] end
    if writeUid(dest,uid) then return true end
  else
    if value=="" then status="Phrase is empty";return false end
    if #value>PHRASE_MAX then status="Phrase > 52 chars";return false end
    if pushMsp(MSP_WRITE,dest,PHRASE_CMD,value) then return true end
  end
  status="Telemetry busy"
  return false
end
local function startSet()
  if phrase=="" then status="Enter phrase first";return end
  if #phrase>PHRASE_MAX then status="Phrase > 52 chars";return end
  if timer=="bothTX" or timer=="unbindDone" then status="Finish current operation first";return end
  if target==TARGET_BOTH then
    bindRefreshRx=false;uidTimeoutRecovery=false
    abandonUidRequest()
    uidFrom=nil
    bothPhrase=phrase
    status="Setting RX..."
    bothRxWriteQueued=setOne(TARGET_RX,bothPhrase)
    if bothRxWriteQueued then historyAdd(bothPhrase)
    else status="RX write busy; continuing with TX..." end
    schedule(WRITE_SETTLE,"bothTX")
  else
    if target==TARGET_RX and linkState~=LINK_UP then status="RX link not active";return end
    bindRefreshRx=false;uidTimeoutRecovery=false
    abandonUidRequest()
    uidFrom=nil
    status=(target==TARGET_TX) and "Setting TX..." or "Setting RX..."
    if setOne(target) then historyAdd(phrase);schedule(WRITE_SETTLE,"readBack") end
  end
end
local function processTimer()
  if not timer or getTime()-timerAt<timerTicks then return end
  local k=timer;cancel()
  if k=="uid" then retryUid()
  elseif k=="bothTX" then
    target=TARGET_TX
    status=(attempts==0) and "Setting TX..." or "Retrying TX..."
    if setOne(TARGET_TX,bothPhrase) then
      if history[1]~=bothPhrase then historyAdd(bothPhrase) end
      attempts=0
      if bothRxWriteQueued then
        status="Phrase sent"
        bothRxWriteQueued=nil
        bothPhrase=nil
        schedule(WRITE_SETTLE,"readBack")
      else
        status="TX sent; RX write busy"
        bothRxWriteQueued=nil
        bothPhrase=nil
      end
    else
      attempts=attempts+1
      if attempts<MAX_RETRY then
        status=bothRxWriteQueued and "RX set; retrying TX..." or "Retrying TX..."
        schedule(RETRY,"bothTX")
      else
        status=bothRxWriteQueued and "RX set; TX write busy" or "RX and TX writes busy"
        attempts=0
        bothRxWriteQueued=nil
        bothPhrase=nil
      end
    end
  elseif k=="readBack" then
    bothRxWriteQueued=nil
    bothPhrase=nil
    attempts=0
    uidReadDest=nil
    startUidRead()
  elseif k=="autoUid" then startUidRead()
  elseif k=="bindDone" then
    if bindRefreshRx then status="Bind sent, waiting RX..." else status="Bind sent" end
  elseif k=="unbindDone" then
    if linkState==LINK_WAIT_DOWN then
      if linkCandidate==LINK_UP and linkSamples>=LINK_CONFIRM_SAMPLES then
        linkState=LINK_UP
        status="RX still connected"
      else
        linkState=LINK_UNKNOWN
        status="Unbind sent"
      end
      linkCandidate=nil;linkSamples=0
    else
      status="Unbind sent"
    end
  end
end

-- ---------------------------------------------------------------------------
-- FreedomTX / B&W-only UI. Color, LVGL, touch and animation code removed.
-- ---------------------------------------------------------------------------
local function buildRows()
  if rowsTarget==target then return end
  rowsTarget=target
  -- Reuse the main-page row table; History uses its own lazy numeric state.
  for i=#bwRows,1,-1 do bwRows[i]=nil end
  bwRows[1]=ROW_PHRASE;bwRows[2]=ROW_TARGET;bwRows[3]=ROW_UID;bwRows[4]=ROW_SET
  if target==TARGET_RX then bwRows[#bwRows+1]=ROW_LINK end
  bwRows[#bwRows+1]=ROW_HISTORY
  bwRows[#bwRows+1]=ROW_EXIT
end
local function adjustScroll()
  local pos=1
  for i=1,#bwRows do if bwRows[i]==selected then pos=i;break end end
  if pos<bwFirst then bwFirst=pos end
  if pos>bwFirst+VISIBLE_ROWS-1 then bwFirst=pos-VISIBLE_ROWS+1 end
  local m=math.max(1,#bwRows-VISIBLE_ROWS+1)
  if bwFirst>m then bwFirst=m end
end
local function draw()
  lcd.clear()
  lcd.drawFilledRectangle(0,0,LCD_W,9,GREY_DEFAULT)
  lcd.drawText(1,1,"ELRS Bind",INVERS)
  lcd.drawText(LCD_W-1,1,linkState==LINK_UP and "C" or "-",INVERS+RIGHT+BOLD)
  adjustScroll()
  local y=11
  local last=math.min(#bwRows,bwFirst+VISIBLE_ROWS-1)
  for i=bwFirst,last do
    local id=bwRows[i]
    local a=(id==selected) and INVERS or 0
    if id==ROW_PHRASE then lcd.drawText(0,y,"Phrase");editorDraw(phraseEditor,COL2,y,a)
    elseif id==ROW_TARGET then lcd.drawText(0,y,"Target");lcd.drawText(COL2,y,(target==TARGET_TX and "TX" or (target==TARGET_RX and "RX" or "Both")),a)
    elseif id==ROW_UID then
      if not uidFrom then lcd.drawText(0,y,"UID: ---",a+SMLSIZE)
      else lcd.drawText(0,y,((uidFrom==RX) and "RX " or "TX ")..uid[1]..","..uid[2]..","..uid[3]..","..uid[4]..","..uid[5]..","..uid[6],a+SMLSIZE) end
    elseif id==ROW_SET then lcd.drawText(10,y,"[Set]",a+BOLD)
    elseif id==ROW_LINK then lcd.drawText(10,y,linkState==LINK_UP and "[Unbind]" or "[Bind]",a+BOLD)
    elseif id==ROW_HISTORY then lcd.drawText(0,y,"> History",a+BOLD)
    elseif id==ROW_EXIT then lcd.drawText(10,y,"[---- EXIT ----]",a+BOLD)
    end
    y=y+8
  end
  if status~=bwLastStatus then bwLastStatus=status;bwStatusAt=getTime() end
  if status and getTime()-bwStatusAt<BW_STATUS_TICKS then
    local n=math.floor((LCD_W-2)/5)
    local st=(#status>n) and string.sub(status,1,n) or status
    lcd.drawFilledRectangle(0,LCD_H-8,LCD_W,8,ERASE)
    lcd.drawText(0,LCD_H-8,st,SMLSIZE)
  end
end
local function drawHistory()
  lcd.clear()
  lcd.drawFilledRectangle(0,0,LCD_W,9,GREY_DEFAULT)
  lcd.drawText(1,1,"Bind History",INVERS)
  if historyConfirm then
    lcd.drawText(0,18,"Clear all history?",0)
    lcd.drawText(0,34,"ENTER: Confirm",BOLD)
    lcd.drawText(0,44,"EXIT: Cancel",BOLD)
    return
  end
  local count=#history+2
  if historySelected<historyFirst then historyFirst=historySelected end
  if historySelected>historyFirst+VISIBLE_ROWS-1 then historyFirst=historySelected-VISIBLE_ROWS+1 end
  local y=11
  for pos=historyFirst,math.min(count,historyFirst+VISIBLE_ROWS-1) do
    local a=(pos==historySelected) and INVERS or 0
    if pos<=#history then
      local v=history[pos];local n=math.floor((LCD_W-2)/6)
      if #v>n then v=string.sub(v,1,n) end
      lcd.drawText(0,y,v,a)
    elseif pos==#history+1 then lcd.drawText(10,y,"[Clear All]",a+BOLD)
    else lcd.drawText(10,y,"[---- BACK ----]",a+BOLD) end
    y=y+8
  end
end
local function handleHistory(event)
  if historyConfirm then
    if event==EVT_VIRTUAL_ENTER then
      historyClear();historyConfirm=nil;historySelected=1;historyFirst=1
    elseif event==EVT_VIRTUAL_EXIT then
      historyConfirm=nil
    end
    forceRedraw=true;return
  end
  local count=#history+2
  if event==EVT_VIRTUAL_EXIT then
    historyOpen=false;historySelected=nil;historyFirst=nil
    collectgarbage();forceRedraw=true;return
  elseif isNextEvent(event) then historySelected=historySelected%count+1
  elseif isPrevEvent(event) then historySelected=(historySelected-2)%count+1
  elseif event==EVT_VIRTUAL_ENTER_LONG and historySelected<=#history then
    killEvents(event);historyRemove(historySelected);historySelected=math.min(historySelected,#history+2)
  elseif event==EVT_VIRTUAL_ENTER then
    if historySelected<=#history then
      phrase=history[historySelected];phraseEditor.value=phrase;status="History loaded"
      historyOpen=false;historySelected=nil;historyFirst=nil
      collectgarbage()
    elseif historySelected==#history+1 then historyConfirm=true
    else historyOpen=false;historySelected=nil;historyFirst=nil;collectgarbage() end
  end
  if event~=0 then forceRedraw=true end
end
local function handle(event)
  if edit=="phrase" then
    if editorEvent(phraseEditor,event) then phrase=phraseEditor.value;edit=nil;status="Phrase updated" end
    forceRedraw=true;return
  elseif edit=="target" then
    if isNextEvent(event) then changeTarget(target+1)
    elseif isPrevEvent(event) then changeTarget(target-1)
    elseif event==EVT_VIRTUAL_ENTER or event==EVT_VIRTUAL_EXIT then edit=nil end
    forceRedraw=true;return
  end
  buildRows()
  if event==EVT_VIRTUAL_EXIT then exitRequested=true;return end
  if isNextEvent(event) or isPrevEvent(event) then
    local pos=1
    for i=1,#bwRows do if bwRows[i]==selected then pos=i;break end end
    if isNextEvent(event) then pos=pos%#bwRows+1 else pos=(pos-2)%#bwRows+1 end
    selected=bwRows[pos];forceRedraw=true;return
  end
  if event~=EVT_VIRTUAL_ENTER then return end
  if selected==ROW_PHRASE then phraseEditor.value=phrase;phraseEditor.editing=true;phraseEditor.cur=1;phraseEditor.first=1;edit="phrase"
  elseif selected==ROW_TARGET then edit="target"
  elseif selected==ROW_UID then startUidRead()
  elseif selected==ROW_SET then startSet()
  elseif selected==ROW_LINK and target==TARGET_RX then
    if timer=="unbindDone" then status="Finish current operation first";return end
    if linkState==LINK_UP then
      -- RX_BIND requests bind mode; it does not erase the stored UID.
      local previousLinkState=linkState
      abandonUidRequest()
      status="Sending unbind..."
      bindRefreshRx=false
      linkState=LINK_WAIT_DOWN
      linkCandidate=nil
      linkSamples=0
      if crossfireTelemetryPush(COMMAND,bindRx) then
        schedule(FOLLOW,"unbindDone")
      else
        linkState=previousLinkState
        status="Telemetry busy"
      end
    else
      abandonUidRequest()
      status="Sending bind..."
      bindRefreshRx=true
      if crossfireTelemetryPush(COMMAND,bindTx) then
        schedule(FOLLOW,"bindDone")
      else
        bindRefreshRx=false
        status="Telemetry busy"
      end
    end
  elseif selected==ROW_HISTORY then
    historyOpen=true;historySelected=1;historyFirst=1;historyConfirm=nil
    collectgarbage()
  elseif selected==ROW_EXIT then exitRequested=true end
  forceRedraw=true
end
local function init()
  selected=ROW_PHRASE;target=TARGET_TX;rowsTarget=0
  historyLoad();phrase=history[1] or "";phraseEditor.value=phrase
  bwFirst=1;bwLastStatus=nil;bwStatusAt=getTime()
  historyOpen=false;historySelected=nil;historyFirst=nil;historyConfirm=nil
  forceRedraw=true;lastStatus=nil;lastLink=nil
  uidFrom=nil;uidReadDest=nil;uidGuardUntil=0
  elrsStatusSeen=false;elrsStatusAt=0;elrsStatusPollAt=-ELRS_STATUS_POLL
  linkState=LINK_UNKNOWN;linkCandidate=nil;linkSamples=0;bindRefreshRx=false;uidTimeoutRecovery=false
  status="Reading UID...";attempts=0;cancel();edit=nil;exitRequested=false
  bothRxWriteQueued=nil
  bothPhrase=nil
  collectgarbage()
  schedule(1,"autoUid")
end
local function run(event)
  if event==nil then return 2 end
  drain();processTimer();requestElrsStatus()
  if historyOpen then
    handleHistory(event)
    if historyOpen and (event~=0 or forceRedraw) then drawHistory();forceRedraw=false end
    return 0
  end
  if event~=0 then
    handle(event)
    -- Open History immediately in the same event cycle.
    if historyOpen then
      drawHistory()
      forceRedraw=false
      return 0
    end
  end
  local link=linkState==LINK_UP
  if event~=0 or forceRedraw or status~=lastStatus or link~=lastLink then
    buildRows();draw();lastStatus=status;lastLink=link;forceRedraw=false
  end
  if exitRequested then return 2 end
  return 0
end
return {init=init,run=run}
