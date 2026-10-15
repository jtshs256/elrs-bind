-- TNS|ExpressLRS Bind|TNE
---- ##########################################################################
---- #                                                                        #
---- # ExpressLRS bind phrase manager for BW and color LCD radios             #
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

local VERSION="1.0-C"
local IS_COLOR=(LCD_W>=400 and LCD_H>=200)
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
local BOTH_TX_RETRY_LIMIT=3

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
local bothStep=nil
local bothTxAttempts=0
-- Keep the delayed/retried TX write identical to the earlier RX write.
local bothPhrase=nil
local bothRxWriteQueued=nil
local bothTxWriteQueued=nil
local rxSeen=false
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
local uidRequestActive=false
local uidQuarantineAt=nil
local uidLastRequestAt=nil
local UID_LATE_RESPONSE_GUARD=RETRY*MAX_RETRY
local selected=1
local exitRequested=false
local edit=nil
local targetDropdown=false
local targetDropdownHeight=0
local targetDropdownTarget=0
local bwPage=nil
local bwRows={}
local bwFirst=1
-- Give 128x96 monochrome radios (including the TBS Tango 2) the extra
-- vertical rows their display supports while preserving the 64px layout.
local BW_MAIN_ROWS=(LCD_H>=96) and 9 or 6
local BW_HISTORY_ROWS=(LCD_H>=96) and 9 or 6
local bwLastStatus=nil
local bwStatusAt=0
local BW_STATUS_TICKS=300
local confirm=nil
local colorConfirm=nil
local colorHistoryPage=false
local colorHistoryScroll=0
local colorHistoryScrollTarget=0
local colorUnbindPending=false
local colorLinkAction=0
local colorLinkSamples=0
local colorUidRequested=false
-- Reserve the single timer slot until a Set/link-recovery readback completes.
local colorFollowupPending=false
local colorLinkActionAt=0
local COLOR_BIND_TIMEOUT=3000 -- 30 seconds
local COLOR_UNBIND_TIMEOUT=1000 -- 10 seconds
local unbindIgnoreUp=false
local unbindStartedAt=0
local lastRxAlive=false
local history={}

local ROW_PHRASE=1
local ROW_TARGET=2
local ROW_UID=3
local ROW_SET=4
local ROW_BIND=5
local ROW_UNBIND=6
local ROW_EXIT=7
local ROW_HISTORY=8
local ROW_CLEAR=9
local ROW_BACK=10
local HIST_BASE=100
local HISTORY_MAX=5
local HISTORY_PATH="/SCRIPTS/TOOLS/elrs-history.txt"
local PAGE_MAIN=1
local PAGE_HISTORY=2

local COL2=(LCD_W==212) and 110 or 70
local CHARS=" abcdefghijklmnopqrstuvwxyz0123456789_-,."

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
  history={}
  local f=io.open(HISTORY_PATH,"r")
  if not f then return end
  local data=""
  while true do
    local part=io.read(f,128)
    if not part or #part==0 then break end
    data=data..part
  end
  io.close(f)
  local pos=1
  while pos<=#data do
    local nl=string.find(data,"\n",pos,true)
    local line
    if nl then line=string.sub(data,pos,nl-1);pos=nl+1 else line=string.sub(data,pos);pos=#data+1 end
    if #line>0 and string.byte(line,#line)==13 then line=string.sub(line,1,#line-1) end
    local eq=string.find(line,"=",1,true)
    if eq then
      local key=string.sub(line,1,eq-1)
      local value=string.sub(line,eq+1)
      local idx=tonumber(string.sub(key,2))
      if string.sub(key,1,1)=="h" and idx and idx>=1 and idx<=HISTORY_MAX and value~="" then history[idx]=value end
    end
  end
  local compact={}
  for i=1,HISTORY_MAX do if history[i] then compact[#compact+1]=history[i] end end
  history=compact
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
local function historyClear() history={};historySave() end

-- ---------------------------------------------------------------------------
-- Timer / link helpers
-- ---------------------------------------------------------------------------
local function schedule(t,k) timerAt=getTime();timerTicks=t;timer=k end
local function cancel() timer=nil end
local function endUidRequest()
  if uidRequestActive and uidLastRequestAt then
    uidQuarantineAt=uidLastRequestAt
  end
  uidReadDest=nil
  uidRequestActive=false
  uidLastRequestAt=nil
  attempts=0
  if timer=="uid" then cancel() end
end
local function acceptLinkSample(connected)
  local sample=connected and LINK_UP or LINK_DOWN
  -- Ignore delayed UP frames after Unbind even if status polling temporarily
  -- marks the link state unknown. The guard expires if Unbind did not work.
  if unbindIgnoreUp and sample==LINK_UP then
    if getTime()-unbindStartedAt<COLOR_UNBIND_TIMEOUT then
      linkCandidate=nil;linkSamples=0
      return
    end
    unbindIgnoreUp=false
  end
  if linkCandidate==sample then linkSamples=linkSamples+1
  else linkCandidate=sample;linkSamples=1 end
  if linkSamples>=LINK_CONFIRM_SAMPLES then
    linkState=sample
    if sample==LINK_DOWN then unbindIgnoreUp=false end
    linkCandidate=nil
    linkSamples=0
    if sample==LINK_UP and (bindRefreshRx or uidTimeoutRecovery) then
      bindRefreshRx=false
      uidTimeoutRecovery=false
      target=TARGET_RX
      uidReadDest=nil
      uidRequestActive=false
      attempts=0
      status="RX linked, reading UID..."
      if IS_COLOR then
        colorLinkAction=0
        colorLinkActionAt=0
        colorUnbindPending=false
        colorUidRequested=true
        -- Keep focus on the action only when it was still on Bind as the
        -- asynchronous link update arrived. Do not steal focus from Target
        -- (or another control) while the user is navigating the screen.
        if selected==ROW_BIND then selected=ROW_UNBIND end
        colorFollowupPending=true
      end
      schedule(WRITE_SETTLE,"readBack")
    end
  end
end
local function rxAlive() return linkState==LINK_UP end
local function rxReachable()
  return rxAlive() and rxSeen and elrsStatusSeen
      and getTime()-elrsStatusAt<ELRS_STATUS_TIMEOUT
end
local function requestElrsStatus()
  local now=getTime()
  if elrsStatusSeen and now-elrsStatusAt>=ELRS_STATUS_TIMEOUT then
    -- Missing status frames mean the link state is unknown, not confirmed down.
    linkState=LINK_UNKNOWN;linkCandidate=nil;linkSamples=0
  end
  if now-elrsStatusPollAt<ELRS_STATUS_POLL then return end
  -- UID reads, late-reply quarantine, and post-write readback waits can span
  -- multiple status intervals. Keep polling so RX reachability stays current.
  if (timer~=nil and timer~="uid" and timer~="autoUid" and timer~="readBack")
      or (attempts>0 and timer~="uid" and timer~="readBack") then return end
  crossfireTelemetryPush(PARAM_WRITE,{TX,HANDSET,0,0})
  elrsStatusPollAt=now
end
local function targetName()
  if target==TARGET_TX then return "TX" end
  if target==TARGET_RX then return "RX" end
  return "Both"
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
local function mspWrite(frame,dest,args)
  local d={dest,HANDSET,MSP_V1+MSP_START,#args,MSP_FN}
  for i=1,#args do d[5+i]=args[i] end
  return crossfireTelemetryPush(frame,d)
end
local function readUid(dest)
  return mspWrite(MSP_REQ,dest,{UID_CMD})
end
local function writeUid(dest,u)
  return mspWrite(MSP_WRITE,dest,{UID_CMD,u[1],u[2],u[3],u[4],u[5],u[6]})
end
local function writePhrase(dest,s)
  local a={PHRASE_CMD}
  for i=1,#s do a[i+1]=string.byte(s,i) end
  return mspWrite(MSP_WRITE,dest,a)
end

-- ---------------------------------------------------------------------------
-- MSP UID response decoder, copied in behavior from msp.decodeUid().
-- ---------------------------------------------------------------------------
local function decodeUid(d)
  if not d or d[1]~=HANDSET then return nil end
  local st,size,fn=d[3],d[4],d[5]
  if not st or not size or not fn then return nil end
  if d[5+size]==nil then return nil end
  if bit32.band(st,MSP_START)==0 then return nil end
  if bit32.band(st,MSP_VER_MASK)~=MSP_V1 then return nil end
  if fn~=MSP_FN or size<7 or d[6]~=UID_CMD then return nil end
  local decoded={}
  for i=1,6 do decoded[i]=d[6+i] end
  return d[2],decoded
end
local function drain()
  while true do
    local c,d=crossfireTelemetryPop()
    if not c then break end
    if c==ELRS_STATUS and d and d[2]==TX and d[6]~=nil then
      -- Exact crsf.lua decode: ELRS_STATUS flags byte bit 0 is RX connected.
      -- Official CRSF status handling also filters by the expected device ID;
      -- ignore status frames from any other CRSF device on the bus.
      rxSeen=bit32.btest(d[6],1)
      elrsStatusSeen=true
      elrsStatusAt=getTime()
      -- TBS exact path: every ELRS_STATUS sample feeds the link state machine.
      acceptLinkSample(rxSeen)
    end

    if c==MSP_RESP then
      local src,decoded=decodeUid(d)
      -- MSP has no transaction ID. Accept replies only after a UID request was
      -- queued; target changes quarantine the previous request window before
      -- another target is queried.
      if src and uidReadDest and uidRequestActive then
        for i=1,6 do uid[i]=decoded[i] end
        -- Associate the reply with the UID request that is currently
        -- active. Some ELRS/EdgeTX combinations report the routing
        -- address differently, so use the requested target for display.
        uidFrom=uidReadDest or src
        uidTimeoutRecovery=false
        status=nil
        attempts=0
        uidRequestActive=false
        uidLastRequestAt=nil
        uidQuarantineAt=nil
        if timer=="uid" then cancel() end
        if IS_COLOR and uidFrom==RX and linkState==LINK_UP then
          colorLinkAction=0;colorLinkActionAt=0;colorUnbindPending=false;colorUidRequested=false
          lastRxAlive=true
          status="RX UID refreshed"
        end
        elrsStatusPollAt=getTime()-ELRS_STATUS_POLL
      end
    end
  end
end

-- ---------------------------------------------------------------------------
-- UID text parsing. A comma-separated 4..6 byte string is treated as raw UID.
-- ---------------------------------------------------------------------------
local function parseByte(s)
  local i,j=1,#s
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
  local b,p={},1
  while p<=#s do
    local q=string.find(s,",",p,true)
    local part
    if q then part=string.sub(s,p,q-1);p=q+1 else part=string.sub(s,p);p=#s+1 end
    local n=parseByte(part)
    if not n then return nil end
    b[#b+1]=n
  end
  if #b<4 or #b>6 then return nil end
  local u={0,0,0,0,0,0}
  for i=1,#b do u[6-#b+i]=b[i] end
  return u
end
local function uidText()
  return string.format("%d,%d,%d,%d,%d,%d",uid[1],uid[2],uid[3],uid[4],uid[5],uid[6])
end

-- ---------------------------------------------------------------------------
-- B&W text editor from current ELRS text_edit.lua.
-- ---------------------------------------------------------------------------
local function charIndex(c)
  local b=string.byte(c)
  if b and b>=65 and b<=90 then c=string.char(b+32) end
  return string.find(CHARS,c,1,true) or 1
end
local function upper(c) local b=string.byte(c);return b and b>=65 and b<=90 end
local function lower(c) local b=string.byte(c);return b and b>=97 and b<=122 end
local function editorNew(maxLen,visible)
  return {maxLen=maxLen,visible=visible,value="",cur=1,editing=false}
end
local function editorStart(e) e.editing=true;e.cur=1 end
local function editorChar(e)
  local c=string.sub(e.value,e.cur,e.cur)
  return c=="" and " " or c
end
local function editorSet(e,c)
  local v=e.value
  while #v<e.cur-1 do v=v.." " end
  e.value=string.sub(v,1,e.cur-1)..c..string.sub(v,e.cur+1)
end
local function editorCommit(e)
  e.editing=false
  local n=#e.value
  while n>0 and string.byte(e.value,n)==32 do n=n-1 end
  e.value=string.sub(e.value,1,n)
end
local function editorEvent(e,event)
  local c=editorChar(e)
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
    if upper(c) and lower(nc) then nc=string.char(string.byte(nc)-32) end
    editorSet(e,nc);return false
  end
  if event==EVT_VIRTUAL_ENTER then
    if e.cur<e.maxLen then e.cur=e.cur+1;return false end
    editorCommit(e);return true
  end
  if event==EVT_VIRTUAL_ENTER_LONG then
    killEvents(event)
    if c==" " then editorCommit(e);return true end
    if upper(c) then editorSet(e,string.char(string.byte(c)+32))
    elseif lower(c) then editorSet(e,string.char(string.byte(c)-32)) end
    return false
  end
  if event==EVT_VIRTUAL_EXIT then editorCommit(e);return true end
  return false
end
local function editorDraw(e,x,y,attr)
  if not e.editing then
    local s=e.value
    if s=="" then s="---" elseif e.visible and #s>e.visible then s=string.sub(s,1,e.visible) end
    lcd.drawText(x,y,s,attr);return
  end
  local first=1
  if e.visible and e.cur>e.visible then first=e.cur-e.visible+1 end
  local pre=string.sub(e.value,first,e.cur-1)
  local suf=e.visible and string.sub(e.value,e.cur+1,first+e.visible-1) or string.sub(e.value,e.cur+1)
  local charW=6
  lcd.drawText(x,y,pre)
  local px=x+#pre*charW
  lcd.drawText(px,y,editorChar(e),INVERS)
  px=px+charW
  if suf~="" then lcd.drawText(px,y,suf) end
end

-- Color-only editor renderer. Color fonts are variable-width, so the B&W
-- fixed 6-pixel cursor calculation would place the inverted cursor over
-- previously drawn characters. Measure each segment with lcd.sizeText().
local function editorDrawColor(e,x,y,attr)
  if not e.editing then
    local text=e.value
    if text=="" then text="---" end
    lcd.drawText(x,y,text,attr)
    return
  end
  local first=1
  if e.visible and e.cur>e.visible then first=e.cur-e.visible+1 end
  local pre=string.sub(e.value,first,e.cur-1)
  local cur=editorChar(e)
  local suf=e.visible and string.sub(e.value,e.cur+1,first+e.visible-1) or string.sub(e.value,e.cur+1)
  local px=x
  if pre~="" then
    lcd.drawText(px,y,pre,attr)
    local w=lcd.sizeText(pre,attr)
    px=px+w
  end
  -- Keep the cursor highlight, but position it after the measured prefix.
  lcd.drawText(px,y,cur,attr+INVERS)
  local cw=lcd.sizeText(cur,attr)
  px=px+cw
  if suf~="" then lcd.drawText(px,y,suf,attr) end
end

local phraseEditor=editorNew(PHRASE_MAX,math.max(4,math.floor((LCD_W-COL2-2)/6)))

-- ---------------------------------------------------------------------------
-- Operations.
-- ---------------------------------------------------------------------------
local startUidRead

local function clearUid()
  uid[1]=0
  uid[2]=0
  uid[3]=0
  uid[4]=0
  uid[5]=0
  uid[6]=0
  uidFrom=nil
end

local function changeTarget(newTarget)
  if newTarget<TARGET_TX then
    newTarget=TARGET_BOTH
  elseif newTarget>TARGET_BOTH then
    newTarget=TARGET_TX
  end

  if IS_COLOR and colorFollowupPending then
    status="Finish current operation first"
    return
  end

  local bothTxPending=(bothStep=="TX")
  if uidReadDest and uidRequestActive and uidLastRequestAt then
    uidQuarantineAt=uidLastRequestAt
  end
  target=newTarget
  colorUnbindPending=false;colorLinkAction=0;colorLinkActionAt=0;colorLinkSamples=0;colorUidRequested=false
  bindRefreshRx=false;uidTimeoutRecovery=false
  bothStep=nil;bothTxAttempts=0;bothPhrase=nil;bothRxWriteQueued=nil;bothTxWriteQueued=nil
  lastRxAlive=false
  clearUid()
  uidReadDest=nil
  uidRequestActive=false
  uidLastRequestAt=nil
  cancel()
  attempts=0

  if target==TARGET_TX or target==TARGET_RX then
    startUidRead()
  else
    status="Target: Both"
  end
  if bothTxPending then status="RX set; TX incomplete" end
end

startUidRead=function()
  if IS_COLOR and (colorFollowupPending or colorLinkAction~=0) then
    status="Finish current operation first"
    return
  end
  -- A new read must not inherit replies from an older in-flight request.
  if uidRequestActive then endUidRequest() end
  if target==TARGET_BOTH then
    clearUid()
    status="Target: Both"
    cancel()
    return
  end

  -- RX only answers while telemetry confirms a live link. Avoid spending
  -- retries and queue space while the receiver is offline.
  if target==TARGET_RX and not rxReachable() then
    clearUid()
    uidReadDest=nil
    uidRequestActive=false
    attempts=0
    cancel()
    uidTimeoutRecovery=true
    status="RX link not active"
    return
  end

  if uidQuarantineAt then
    local elapsed=getTime()-uidQuarantineAt
    if elapsed<UID_LATE_RESPONSE_GUARD then
      schedule(UID_LATE_RESPONSE_GUARD-elapsed,"autoUid")
      status="Waiting for previous UID reply..."
      return
    end
    uidQuarantineAt=nil
  end

  uidReadDest=(target==TARGET_RX) and RX or TX
  clearUid()
  attempts=1
  status="Reading "..targetName().." UID..."
  elrsStatusPollAt=getTime()
  uidRequestActive=readUid(uidReadDest) and true or false
  uidLastRequestAt=uidRequestActive and getTime() or nil
  if not uidRequestActive then status="Telemetry busy" end
  schedule(RETRY,"uid")
end
local function retryUid()
  if attempts>=MAX_RETRY then
    local requestWasSent=uidRequestActive
    clearUid()
    uidFrom=nil
    status=requestWasSent and "No response" or "Telemetry busy"
    attempts=0
    cancel()
    if uidRequestActive and uidLastRequestAt then uidQuarantineAt=uidLastRequestAt end
    uidReadDest=nil
    uidRequestActive=false
    uidLastRequestAt=nil
    -- Retry automatically only after an RX request actually lost reachability.
    -- A reachable RX that never answers should stop at MAX_RETRY like upstream.
    if target==TARGET_RX and not rxReachable() then uidTimeoutRecovery=true end
    if IS_COLOR and colorLinkAction==3 then
      colorLinkAction=1;colorUidRequested=false;colorLinkSamples=0
      status="Waiting RX link..."
    end
    elrsStatusPollAt=getTime()-ELRS_STATUS_POLL
    return
  end
  if not uidReadDest then
    cancel()
    return
  end
  if readUid(uidReadDest) then
    uidRequestActive=true
    uidLastRequestAt=getTime()
    status="Reading "..targetName().." UID..."
  elseif not uidRequestActive then
    status="Telemetry busy"
  end
  attempts=attempts+1
  schedule(RETRY,"uid")
end
local function setOne(which,phraseOverride)
  local dest=(which==TARGET_TX) and TX or RX
  local value=phraseOverride
  if value==nil then value=phrase end
  local u=parseUidText(value)
  if u then
    if not writeUid(dest,u) then status="Telemetry busy";return false end
  else
    if value=="" then status="Phrase is empty";return false end
    if #value>PHRASE_MAX then status="Phrase > 52 chars";return false end
    if not writePhrase(dest,value) then status="Telemetry busy";return false end
  end
  return true
end
local function startSet()
  if IS_COLOR and (colorFollowupPending or colorLinkAction~=0) then
    status="Finish current operation first"
    return
  end
  if phrase=="" then status="Enter phrase first";return end
  if #phrase>PHRASE_MAX then status="Phrase > 52 chars";return end
  if target==TARGET_BOTH then
    bothPhrase=phrase
    bothTxWriteQueued=nil
    bothStep="RX";bothTxAttempts=0;status="Setting RX..."
    bothRxWriteQueued=setOne(TARGET_RX,bothPhrase)
    historyAdd(bothPhrase)
    endUidRequest()
    if IS_COLOR then
      colorFollowupPending=true
      bindRefreshRx=false;uidTimeoutRecovery=false
    end
    bothStep="TX"
    schedule(FOLLOW,"bothTX")
  else
    if target==TARGET_RX and not rxReachable() then status="RX link not active";return end
    status=(target==TARGET_TX) and "Setting TX..." or "Setting RX..."
    if setOne(target) then
      historyAdd(phrase)
      endUidRequest()
      if IS_COLOR then
        colorFollowupPending=true
        bindRefreshRx=false;uidTimeoutRecovery=false
      end
      schedule(FOLLOW,"setDone")
    end
  end
end
local function sendBind(dest)
  return crossfireTelemetryPush(COMMAND,{dest,HANDSET,CMD_RX,CMD_BIND})
end
local function doBind()
  if IS_COLOR and colorFollowupPending then
    colorLinkAction=0;colorLinkActionAt=0;colorUnbindPending=false
    status="Finish current operation first"
    return false
  end
  status="Sending bind..."
  bindRefreshRx=true
  if IS_COLOR and colorLinkAction==1 then colorLinkActionAt=getTime() end
  if not sendBind(TX) then
    bindRefreshRx=false
    colorLinkAction=0;colorLinkActionAt=0;colorUnbindPending=false
    status="Telemetry busy"
    return false
  end
  endUidRequest()
  schedule(FOLLOW,"bindDone")
  return true
end
local function doUnbind()
  if IS_COLOR and colorFollowupPending then
    colorLinkAction=0;colorLinkActionAt=0;colorUnbindPending=false
    status="Finish current operation first"
    return false
  end
  local previousLinkState=linkState
  status="Sending unbind..."
  bindRefreshRx=false
  uidTimeoutRecovery=false
  linkState=LINK_WAIT_DOWN
  unbindIgnoreUp=true
  unbindStartedAt=getTime()
  linkCandidate=nil
  linkSamples=0
  if IS_COLOR and colorLinkAction==2 then colorLinkActionAt=getTime() end
  if not sendBind(RX) then
    linkState=previousLinkState
    unbindIgnoreUp=false
    colorLinkAction=0;colorLinkActionAt=0;colorUnbindPending=false
    status="Telemetry busy"
    return false
  end
  endUidRequest()
  schedule(FOLLOW,"unbindDone")
  return true
end
local function processTimer()
  if not timer or getTime()-timerAt<timerTicks then return end
  local k=timer;cancel()
  if k=="uid" then retryUid()
  elseif k=="bothTX" then
    -- The official follow-up changes the selected target to TX before writing.
    target=TARGET_TX
    status=(bothTxAttempts==0) and "Setting TX..." or "Retrying TX..."
    if setOne(TARGET_TX,bothPhrase) then
      bothTxWriteQueued=true
      bothStep=nil;bothTxAttempts=0
      bothPhrase=nil
      schedule(FOLLOW,"setDone")
    else
      bothTxAttempts=bothTxAttempts+1
      if bothTxAttempts<BOTH_TX_RETRY_LIMIT then
        status="RX set; retrying TX..."
        schedule(RETRY,"bothTX")
      else
        bothTxWriteQueued=false
        bothStep=nil;bothTxAttempts=0;bothPhrase=nil
        schedule(FOLLOW,"setDone")
      end
    end
  elseif k=="setDone" then
    if bothTxWriteQueued==false then
      status=bothRxWriteQueued and "RX write queued; TX busy" or "RX and TX writes busy"
    elseif bothRxWriteQueued==false then
      status="TX sent; RX write busy"
    else
      status="Sent"
    end
    schedule(1,"readBack")
  elseif k=="readBack" then
    colorFollowupPending=false
    attempts=0;uidReadDest=nil;uidRequestActive=false;startUidRead()
    bothRxWriteQueued=nil;bothTxWriteQueued=nil
  elseif k=="autoUid" then startUidRead()
  elseif k=="colorReadUid" then target=TARGET_RX;startUidRead()
  elseif k=="bindDone" then
    if not IS_COLOR or colorLinkAction==0 then status="Bind sent" end
  elseif k=="unbindDone" then
    if not IS_COLOR or colorLinkAction==0 then status="Unbind sent" end
  end
end

-- ---------------------------------------------------------------------------
-- UI.
-- B&W: compact 212x64/128x64 layout.
-- Color: native 480x272-style card layout.  Navigation/events stay identical.
-- ---------------------------------------------------------------------------
local function rgb(r,g,b) return lcd.RGB(r,g,b) end

local C_BG=IS_COLOR and rgb(230,239,247) or 0
local C_PANEL=IS_COLOR and rgb(255,255,255) or 0
local C_BORDER=IS_COLOR and rgb(205,211,220) or 0
local C_TEXT=IS_COLOR and rgb(35,42,52) or 0
local C_MUTED=IS_COLOR and rgb(105,115,128) or 0
local C_BLUE=IS_COLOR and rgb(45,110,210) or 0
local C_GREEN=IS_COLOR and rgb(35,155,90) or 0
local C_ORANGE=IS_COLOR and rgb(225,135,35) or 0
local C_RED=IS_COLOR and rgb(205,65,65) or 0
local C_SEL=IS_COLOR and rgb(220,235,255) or 0
local C_TITLE=IS_COLOR and rgb(30,101,158) or 0
local C_WHITE=IS_COLOR and rgb(255,255,255) or 0
local C_LIGHTBLUE=IS_COLOR and rgb(145,211,244) or 0
local C_FOCUS_BORDER=IS_COLOR and rgb(0,153,230) or 0
local C_BUTTON_TEXT=IS_COLOR and rgb(0,91,170) or 0
local C_LIGHTRED=IS_COLOR and rgb(244,180,180) or 0
local C_FOCUS_RED=IS_COLOR and rgb(205,65,65) or 0

local function roundedFill(x,y,w,h,r,color)
  if not color then return end
  if w<=2*r or h<=2*r then
    lcd.drawFilledRectangle(x,y,w,h,color)
    return
  end
  lcd.drawFilledRectangle(x+r,y,w-2*r,h,color)
  lcd.drawFilledRectangle(x,y+r,w,h-2*r,color)
  lcd.drawFilledCircle(x+r,y+r,r,color)
  lcd.drawFilledCircle(x+w-r-1,y+r,r,color)
  lcd.drawFilledCircle(x+r,y+h-r-1,r,color)
  lcd.drawFilledCircle(x+w-r-1,y+h-r-1,r,color)
end
local function box(x,y,w,h,fill,border)
  -- Color-only rounded box with a 2 px border.
  local r=4
  local bw=2
  if border then roundedFill(x,y,w,h,r,border) end
  if fill then
    if border and w>2*bw and h>2*bw then
      roundedFill(x+bw,y+bw,w-2*bw,h-2*bw,math.max(1,r-bw),fill)
    else
      roundedFill(x,y,w,h,r,fill)
    end
  end
end

local function drawTitle()
  if not IS_COLOR then
    lcd.drawFilledRectangle(0,0,LCD_W,9,GREY_DEFAULT)
    lcd.drawText(1,1,"ELRS Bind "..VERSION,INVERS)
    lcd.drawText(LCD_W-1,1,rxAlive() and "C" or "-",INVERS+RIGHT)
    return
  end
  lcd.drawFilledRectangle(0,0,LCD_W,38,C_BLUE)
  lcd.drawText(18,7,"ExpressLRS",C_WHITE+BOLD+DBLSIZE)
  lcd.drawText(18,25,"Bind / UID Tool",C_WHITE+SMLSIZE)
  lcd.drawText(LCD_W-18,12,rxAlive() and "RX LINK" or "NO RX",C_WHITE+BOLD+RIGHT)
end

local function uidLine()
  if not uidFrom then return "UID: ---" end
  local prefix=(uidFrom==RX) and "RX" or "TX"
  return string.format("%s  %d,%d,%d,%d,%d,%d",prefix,uid[1],uid[2],uid[3],uid[4],uid[5],uid[6])
end

local function buildBwRows()
  bwRows={}
  if bwPage==PAGE_MAIN then
    bwRows={ROW_PHRASE,ROW_TARGET,ROW_UID,ROW_SET}
    if target==TARGET_RX then bwRows[#bwRows+1]=rxAlive() and ROW_UNBIND or ROW_BIND end
    bwRows[#bwRows+1]=ROW_HISTORY
    bwRows[#bwRows+1]=ROW_EXIT
  else
    for i=1,#history do bwRows[#bwRows+1]=HIST_BASE+i end
    bwRows[#bwRows+1]=ROW_CLEAR
    bwRows[#bwRows+1]=ROW_BACK
  end
end
local function bwVisibleRows()
  return (bwPage==PAGE_HISTORY) and BW_HISTORY_ROWS or BW_MAIN_ROWS
end
local function adjustBwScroll()
  local visible=bwVisibleRows()
  local pos=1
  for i=1,#bwRows do
    if bwRows[i]==selected then pos=i;break end
  end
  if pos<bwFirst then bwFirst=pos end
  if pos>bwFirst+visible-1 then bwFirst=pos-visible+1 end
  local maxFirst=math.max(1,#bwRows-visible+1)
  if bwFirst>maxFirst then bwFirst=maxFirst end
  if bwFirst<1 then bwFirst=1 end
end

local function drawBW()
  lcd.drawFilledRectangle(0,0,LCD_W,9,GREY_DEFAULT)
  lcd.drawText(1,1,bwPage==PAGE_MAIN and "ELRS Bind" or "Bind History",INVERS)
  -- Match lcd.lua: show current receiver link state at the top-right.
  lcd.drawText(LCD_W-1,1,rxAlive() and "C" or "-",INVERS+RIGHT)
  buildBwRows()
  adjustBwScroll()
  local y=11
  local last=math.min(#bwRows,bwFirst+bwVisibleRows()-1)
  for i=bwFirst,last do
    local id=bwRows[i]
    local a=(id==selected) and INVERS or 0
    if id==ROW_PHRASE then lcd.drawText(0,y,"Phrase");editorDraw(phraseEditor,COL2,y,a)
    elseif id==ROW_TARGET then lcd.drawText(0,y,"Target");lcd.drawText(COL2,y,targetName(),a)
    elseif id==ROW_UID then lcd.drawText(0,y,uidLine(),a+SMLSIZE)
    elseif id==ROW_SET then lcd.drawText(10,y,"[Set]",a+BOLD)
    elseif id==ROW_BIND then lcd.drawText(10,y,"[Bind]",a+BOLD)
    elseif id==ROW_UNBIND then lcd.drawText(10,y,"[Unbind]",a+BOLD)
    elseif id==ROW_HISTORY then lcd.drawText(0,y,"> History",a+BOLD)
    elseif id==ROW_EXIT then lcd.drawText(10,y,"[---- EXIT ----]",a+BOLD)
    elseif id==ROW_CLEAR then lcd.drawText(10,y,"[Clear All]",a+BOLD)
    elseif id==ROW_BACK then lcd.drawText(10,y,"[---- BACK ----]",a+BOLD)
    elseif id>HIST_BASE then
      local v=history[id-HIST_BASE] or ""
      local maxChars=math.floor((LCD_W-2)/6)
      if #v>maxChars then v=string.sub(v,1,maxChars) end
      lcd.drawText(0,y,v,a)
    end
    y=y+8
  end
  -- Both B&W pages use the full height. Main-page status is a temporary
  -- bottom overlay and automatically disappears after 3 seconds.
  if bwPage==PAGE_MAIN then
    if status~=bwLastStatus then
      bwLastStatus=status
      bwStatusAt=getTime()
    end
    if status and getTime()-bwStatusAt<BW_STATUS_TICKS then
      local maxChars=math.floor((LCD_W-2)/5)
      local st=status
      if #st>maxChars then st=string.sub(st,1,maxChars) end
      lcd.drawFilledRectangle(0,LCD_H-8,LCD_W,8,ERASE)
      lcd.drawText(0,LCD_H-8,st,SMLSIZE)
    end
  end
end
local function colorHistoryWindow()
  local count=math.min(#history,HISTORY_MAX)
  local idx=nil
  if selected>HIST_BASE and selected<=HIST_BASE+HISTORY_MAX then
    idx=selected-HIST_BASE
  elseif selected>HIST_BASE+HISTORY_MAX then
    idx=selected-HIST_BASE-HISTORY_MAX
  elseif selected==ROW_CLEAR then
    idx=count+1
  end
  local first=1
  if selected==ROW_EXIT then
    -- Exit follows Clear All in wheel order. Force the final list position so
    -- Clear All is the bottom visible row even when fast wheel events skip
    -- ahead before the previous animation has completed.
    first=math.max(1,count-2)
  elseif idx and idx>4 then
    first=idx-3
  end
  colorHistoryScrollTarget=(first-1)*36
  local delta=colorHistoryScrollTarget-colorHistoryScroll
  if delta~=0 then
    local step=math.min(12,math.abs(delta))
    colorHistoryScroll=colorHistoryScroll+(delta>0 and step or -step)
  end
  return count
end

local function drawColorMain()
  -- EdgeTX 2.10 emulation of the newer ExpressLRS LVGL layout.
  lcd.drawFilledRectangle(0,0,LCD_W,LCD_H,C_BG)

  -- LVGL-like page title + UID subtitle on a light-blue header.
  lcd.drawFilledRectangle(0,0,LCD_W,48,C_TITLE)
  lcd.drawFilledRectangle(0,46,LCD_W,2,C_BLUE)
  lcd.drawText(10,5,"ExpressLRS Bind Phrase",C_WHITE+BOLD)
  lcd.drawText(LCD_W-10,5,linkState==LINK_UP and "C" or "-",C_WHITE+BOLD+RIGHT)
  -- UID is intentionally larger and more prominent.
  lcd.drawText(10,25,uidLine(),C_WHITE+SMLSIZE)

  -- First LVGL-like setting row: Bind phrase + text edit + Set.
  local row1y=44
  lcd.drawText(10,row1y+17,"Bind phrase",C_TEXT)
  local phraseSel=(selected==ROW_PHRASE)
  local editX,editY,editW,editH=110,row1y+10,260,32
  box(editX,editY,editW,editH,phraseSel and C_SEL or C_WHITE,phraseSel and C_FOCUS_BORDER or C_LIGHTBLUE)
  editorDrawColor(phraseEditor,editX+9,editY+6,phraseSel and C_BLUE or C_TEXT)
  local setSel=(selected==ROW_SET)
  box(LCD_W-100,editY,90,editH,setSel and C_SEL or C_WHITE,setSel and C_FOCUS_BORDER or C_LIGHTBLUE)
  lcd.drawText(LCD_W-55,editY+6,"Set",C_BUTTON_TEXT+CENTER)

  -- Second LVGL-like setting row: Target + choice + Request UID + conditional Unbind.
  local row2y=80
  lcd.drawText(10,row2y+17,"Target",C_TEXT)
  local targetSel=(selected==ROW_TARGET)
  box(110,row2y+10,125,32,targetSel and C_SEL or C_WHITE,targetSel and C_FOCUS_BORDER or C_LIGHTBLUE)
  local longNames={"Transmitter","Receiver","Both"}
  lcd.drawText(120,row2y+16,"v",C_BUTTON_TEXT)
  lcd.drawText(178,row2y+16,longNames[target],C_BUTTON_TEXT+CENTER)

  local uidEnabled=(target~=TARGET_BOTH) and (target~=TARGET_RX or rxAlive())
  local uidSel=uidEnabled and (selected==ROW_UID)
  box(245,row2y+10,125,32,uidSel and C_SEL or C_WHITE,uidEnabled and (uidSel and C_FOCUS_BORDER or C_LIGHTBLUE) or C_BORDER)
  lcd.drawText(307,row2y+16,"Request UID",(uidEnabled and C_BUTTON_TEXT or C_MUTED)+CENTER)

  local rxConnected=(linkState==LINK_UP)
  if target==TARGET_RX then
    -- Bind and Unbind share one position and are mutually exclusive.
    local actionRow=rxConnected and ROW_UNBIND or ROW_BIND
    local actionText=rxConnected and "Unbind" or "Bind"
    local actionSel=(selected==actionRow)
    if rxConnected then
      -- Unbind uses the same red palette as Exit.
      box(LCD_W-100,row2y+10,90,32,actionSel and C_LIGHTRED or C_WHITE,actionSel and C_FOCUS_RED or C_LIGHTRED)
      lcd.drawText(LCD_W-55,row2y+16,actionText,C_RED+CENTER)
    else
      box(LCD_W-100,row2y+10,90,32,actionSel and C_SEL or C_WHITE,actionSel and C_FOCUS_BORDER or C_LIGHTBLUE)
      lcd.drawText(LCD_W-55,row2y+16,actionText,C_BUTTON_TEXT+CENTER)
    end
  end

  -- Inline history: five saved entries are reachable by the wheel. Three
  -- equal-height rows are shown at once and the viewport follows the selection.
  local historyY=126
  lcd.drawText(10,historyY+7,"History",C_TEXT)
  local historyCount=colorHistoryWindow()
  for i=1,historyCount do
    local y=historyY+(i-1)*36-colorHistoryScroll
    -- Keep the animation inside the three-row history viewport.
    if y>=historyY and y+32<=266 then
      local id=HIST_BASE+i
      local sel=(selected==id)
      box(110,y,LCD_W-220,32,sel and C_SEL or C_WHITE,sel and C_FOCUS_BORDER or C_LIGHTBLUE)
      local shown=history[i]
      if #shown>28 then shown=string.sub(shown,1,28) end
      lcd.drawText(120,y+6,shown,sel and C_BUTTON_TEXT or C_TEXT)
      local delSel=(selected==id+HISTORY_MAX)
      box(LCD_W-100,y,90,32,delSel and C_LIGHTRED or C_WHITE,delSel and C_FOCUS_RED or C_LIGHTRED)
      lcd.drawText(LCD_W-55,y+6,"X",C_RED+BOLD+CENTER)
    end
  end
  if historyCount==0 then
    lcd.drawText(110,historyY+7,"No saved phrases",C_MUTED)
  end
  -- Flat footer. Clear All appears only when history exists.
  lcd.drawText(LCD_W-10,25,status or "Ready",C_WHITE+SMLSIZE+RIGHT)
  if #history>0 then
    local clearSel=(selected==ROW_CLEAR)
    local clearY=historyY+historyCount*36-colorHistoryScroll
    if clearY>=historyY and clearY+32<=266 then
      box(110,clearY,LCD_W-220,32,clearSel and C_LIGHTRED or C_WHITE,clearSel and C_FOCUS_RED or C_LIGHTRED)
      lcd.drawText(240,clearY+6,"Clear All",C_RED+CENTER)
    end
  end
  local exitSel=(selected==ROW_EXIT)
  box(10,234,90,32,exitSel and C_LIGHTRED or C_WHITE,exitSel and C_FOCUS_RED or C_LIGHTRED)
  lcd.drawText(55,240,"Exit",C_RED+CENTER)

  -- Target button and options animate as one joined rounded rectangle.
  if targetDropdown or targetDropdownHeight>0 then
    targetDropdownTarget=targetDropdown and 96 or 0
    local delta=targetDropdownTarget-targetDropdownHeight
    if delta~=0 then
      local step=math.min(96,math.abs(delta))
      targetDropdownHeight=targetDropdownHeight+(delta>0 and step or -step)
    end
    local menuX,menuY,menuW,itemH=110,90,125,32
    local menuH=itemH+targetDropdownHeight
    roundedFill(menuX,menuY,menuW,menuH,4,C_FOCUS_BORDER)
    roundedFill(menuX+2,menuY+2,menuW-4,menuH-4,2,C_WHITE)
    lcd.drawFilledRectangle(menuX+4,menuY+3,menuW-8,itemH-6,C_WHITE)
    lcd.drawText(120,menuY+6,targetDropdown and "^" or "v",C_BUTTON_TEXT)
    lcd.drawText(178,menuY+6,longNames[target],C_BUTTON_TEXT+CENTER)
    if targetDropdownHeight>0 then
      lcd.drawFilledRectangle(menuX+2,menuY+itemH-1,menuW-4,2,C_LIGHTBLUE)
    end
    for i=1,3 do
      local y=menuY+i*itemH
      local visible=math.max(0,math.min(itemH,targetDropdownHeight-(i-1)*itemH))
      if visible>0 then
        local active=(target==i)
        if active then
          if i==1 then
            lcd.drawFilledRectangle(menuX+2,y,menuW-4,math.max(1,visible-2),C_SEL)
          elseif i==3 then
            roundedFill(menuX+2,y,menuW-4,math.max(1,visible-2),2,C_SEL)
          else
            lcd.drawFilledRectangle(menuX+2,y+2,menuW-4,math.max(1,visible-4),C_SEL)
          end
        end
        -- divider moved to top boundary only
        if visible>=itemH then
          lcd.drawText(172,y+6,longNames[i],C_BUTTON_TEXT+CENTER)
        end
      end
    end
  end
end
local function drawColorHistory()
  lcd.drawFilledRectangle(0,0,LCD_W,LCD_H,C_BG)
  lcd.drawFilledRectangle(0,0,LCD_W,48,C_TITLE)
  lcd.drawFilledRectangle(0,46,LCD_W,2,C_BLUE)
  lcd.drawText(10,5,"Bind Phrase History",C_WHITE)
  lcd.drawText(10,25,"Select a phrase to use it",C_WHITE+SMLSIZE)
  for i=1,HISTORY_MAX do
    local value=history[i]
    if value then
      local y=58+(i-1)*34
      local id=HIST_BASE+i
      local sel=(selected==id)
      box(10,y,LCD_W-120,29,sel and C_SEL or C_WHITE,sel and C_FOCUS_BORDER or C_LIGHTBLUE)
      local shown=value
      if #shown>48 then shown=string.sub(shown,1,48) end
      lcd.drawText(20,y+5,shown,sel and C_BLUE or C_TEXT)
      local delSel=(selected==id+HISTORY_MAX)
      box(LCD_W-100,y,90,29,delSel and C_LIGHTRED or C_WHITE,delSel and C_FOCUS_RED or C_LIGHTRED)
      lcd.drawText(LCD_W-55,y+5,"X",C_RED+BOLD+CENTER)
    end
  end
  local clearSel=(selected==ROW_CLEAR)
  box(10,LCD_H-40,90,30,clearSel and C_LIGHTRED or C_WHITE,clearSel and C_FOCUS_RED or C_LIGHTRED)
  lcd.drawText(55,LCD_H-35,"Clear All",C_RED+CENTER)
  local backSel=(selected==ROW_BACK)
  box(LCD_W-100,LCD_H-40,90,30,backSel and C_SEL or C_WHITE,backSel and C_FOCUS_BORDER or C_LIGHTBLUE)
  lcd.drawText(LCD_W-55,LCD_H-35,"Back",C_BUTTON_TEXT+CENTER)
end
local function drawColor()
  drawColorMain()
end

local function draw()
  lcd.clear()
  if IS_COLOR then drawColor() else drawBW() end
end

local function touchIn(x,y,rx,ry,rw,rh)
  return x and y and x>=rx and x<rx+rw and y>=ry and y<ry+rh
end

local function handleBW(event)
  buildBwRows()
  if confirm then
    local result=popupConfirmation(confirm.msg,"PRESS [OK] to confirm",event)
    if not confirm.armed then
      if event==0 then confirm.armed=true end
      return true
    end
    if result=="OK" then
      if confirm.index then historyRemove(confirm.index) else historyClear() end
      confirm=nil;buildBwRows();selected=bwRows[1]
    elseif result=="CANCEL" then confirm=nil end
    return true
  end
  if edit then return false end
  if event==EVT_VIRTUAL_EXIT then
    if bwPage==PAGE_HISTORY then bwPage=PAGE_MAIN;buildBwRows();selected=bwRows[1];bwFirst=1
    else exitRequested=true end
    return true
  end
  if event==EVT_VIRTUAL_ENTER_LONG and bwPage==PAGE_HISTORY and selected>HIST_BASE then
    killEvents(event);confirm={msg="Delete entry?",index=selected-HIST_BASE};return true
  end
  if isNextEvent(event) or isPrevEvent(event) then
    local pos=1
    for i=1,#bwRows do if bwRows[i]==selected then pos=i;break end end
    if isNextEvent(event) then pos=pos%#bwRows+1 else pos=(pos-2)%#bwRows+1 end
    selected=bwRows[pos];adjustBwScroll();return true
  end
  if event==EVT_VIRTUAL_ENTER then
    if selected==ROW_HISTORY then bwPage=PAGE_HISTORY;buildBwRows();selected=bwRows[1];bwFirst=1
    elseif selected==ROW_CLEAR then confirm={msg="Clear history?"}
    elseif selected==ROW_BACK then bwPage=PAGE_MAIN;buildBwRows();selected=bwRows[1];bwFirst=1
    elseif selected>HIST_BASE then
      phrase=history[selected-HIST_BASE] or phrase
      phraseEditor.value=phrase
      status="History loaded"
      bwPage=PAGE_MAIN;buildBwRows();selected=ROW_PHRASE;bwFirst=1
    else return false end
    return true
  end
  return false
end

local function handle(event,touchState)
  if not IS_COLOR and handleBW(event) then return end
  if IS_COLOR and touchState and event==EVT_TOUCH_TAP then
    local x,y=touchState.x,touchState.y
    if targetDropdown then
      for i=1,3 do
        if targetDropdownHeight>=i*32 and touchIn(x,y,110,122+(i-1)*32,125,32) then
          changeTarget(i);targetDropdown=false;edit=nil;selected=ROW_TARGET;return
        end
      end
      targetDropdown=false;edit=nil;selected=ROW_TARGET
      return
    end
    local historyCount=colorHistoryWindow()
    for i=1,historyCount do
      local yy=126+(i-1)*36-colorHistoryScroll
      if yy>=126 and yy+32<=266 then
        if touchIn(x,y,110,yy,LCD_W-220,32) then
          phrase=history[i];phraseEditor.value=phrase;status="History loaded";selected=ROW_PHRASE;return
        elseif touchIn(x,y,LCD_W-100,yy,90,32) then
          historyRemove(i);selected=ROW_EXIT;return
        end
      end
    end
    if #history>0 then
      local clearY=126+historyCount*36-colorHistoryScroll
      if clearY>=126 and clearY+32<=266 and touchIn(x,y,110,clearY,LCD_W-220,32) then
        selected=ROW_CLEAR;colorConfirm={armed=false};return
      end
    end
    if edit=="phrase" then
      if touchIn(x,y,110,54,260,32) then
        local rel=math.max(1,math.min(phraseEditor.maxLen,math.floor((x-119)/7)+1))
        phraseEditor.cur=rel
      else
        editorCommit(phraseEditor);phrase=phraseEditor.value;edit=nil;status="Phrase updated"
      end
      return
    end
    if touchIn(x,y,110,54,260,32) then
      selected=ROW_PHRASE;phraseEditor.value=phrase;editorStart(phraseEditor);edit="phrase";return
    elseif touchIn(x,y,110,90,125,32) then
      selected=ROW_TARGET;targetDropdown=true;edit="target";return
    elseif (target~=TARGET_BOTH) and (target~=TARGET_RX or rxAlive()) and touchIn(x,y,245,90,125,32) then
      if colorFollowupPending or colorLinkAction~=0 then status="Finish current operation first";return end
      selected=ROW_UID;cancel();attempts=0;uidFrom=nil;startUidRead();return
    elseif touchIn(x,y,LCD_W-100,54,90,32) then
      selected=ROW_SET;startSet();return
    elseif target==TARGET_RX and touchIn(x,y,LCD_W-100,90,90,32) then
      if colorLinkAction~=0 then return end
      if not colorUnbindPending and rxAlive() then
        colorUnbindPending=true;colorLinkAction=2;colorLinkSamples=0;colorUidRequested=false
        selected=ROW_BIND
        if doUnbind() then status="Waiting RX disconnect..." end
      else
        colorUnbindPending=false;colorLinkAction=1;colorLinkSamples=0;colorUidRequested=false
        selected=ROW_BIND
        if doBind() then status="Waiting RX link..." end
      end
      return
    elseif touchIn(x,y,10,234,90,32) then
      selected=ROW_EXIT;exitRequested=true;return
    end
  end
  if edit then
    if edit=="phrase" then
      if editorEvent(phraseEditor,event) then phrase=phraseEditor.value;edit=nil;status="Phrase updated" end
    elseif edit=="target" then
      if isNextEvent(event) then
        changeTarget(target+1)
      elseif isPrevEvent(event) then
        changeTarget(target-1)
      elseif event==EVT_VIRTUAL_ENTER or event==EVT_VIRTUAL_EXIT then
        targetDropdown=false;edit=nil;selected=ROW_TARGET
      end
    end
    return
  end
  if isNextEvent(event) or isPrevEvent(event) then
    local rows
    if IS_COLOR then
      rows={ROW_PHRASE,ROW_SET,ROW_TARGET}
      local uidEnabled=(target~=TARGET_BOTH) and (target~=TARGET_RX or rxAlive())
      if uidEnabled then rows[#rows+1]=ROW_UID end
      -- On the color UI, Bind/Unbind follows Request UID in wheel order.
      if target==TARGET_RX then
        if colorLinkAction==0 and not colorUnbindPending and rxAlive() then rows[#rows+1]=ROW_UNBIND
        else rows[#rows+1]=ROW_BIND end
      end
      for i=1,math.min(#history,HISTORY_MAX) do
        rows[#rows+1]=HIST_BASE+i
        rows[#rows+1]=HIST_BASE+HISTORY_MAX+i
      end
      if #history>0 then rows[#rows+1]=ROW_CLEAR end
    else
      rows={ROW_PHRASE,ROW_TARGET,ROW_UID,ROW_SET}
      if target==TARGET_RX then
        if rxAlive() then rows[#rows+1]=ROW_UNBIND
        else rows[#rows+1]=ROW_BIND end
      end
    end
    rows[#rows+1]=ROW_EXIT
    -- The receiver can disconnect while Request UID has focus. If that makes
    -- the button unavailable, anchor navigation at Target so this movement
    -- goes directly to the next enabled control.
    if IS_COLOR and selected==ROW_UID
      and (target==TARGET_BOTH or (target==TARGET_RX and not rxAlive())) then
      selected=ROW_TARGET
    end
    local pos=nil
    for i=1,#rows do if rows[i]==selected then pos=i;break end end
    if not pos then pos=4 end
    if IS_COLOR then
      -- Clamp color-screen wheel navigation at both ends. In particular,
      -- scrolling down on Clear All no longer wraps to the first control.
      if isNextEvent(event) then
        if pos<#rows then pos=pos+1 end
      else
        if pos>1 then pos=pos-1 end
      end
    else
      if isNextEvent(event) then pos=pos%#rows+1
      else pos=(pos-2)%#rows+1 end
    end
    selected=rows[pos]
    if IS_COLOR and selected==ROW_EXIT then
      local count=math.min(#history,HISTORY_MAX)
      colorHistoryScrollTarget=math.max(0,count-3)*36
      colorHistoryScroll=colorHistoryScrollTarget
    end
  elseif event==EVT_VIRTUAL_ENTER then
    if selected==ROW_PHRASE then phraseEditor.value=phrase;editorStart(phraseEditor);edit="phrase"
    elseif selected==ROW_TARGET then targetDropdown=true;edit="target"
    elseif selected==ROW_UID and target~=TARGET_BOTH and (target~=TARGET_RX or rxAlive()) then
      if IS_COLOR and (colorFollowupPending or colorLinkAction~=0) then
        status="Finish current operation first"
        return
      end
      cancel();attempts=0;uidReadDest=nil;uidFrom=nil;clearUid();startUidRead()
    elseif selected==ROW_SET then startSet()
    elseif IS_COLOR and selected==ROW_BIND and target==TARGET_RX and colorLinkAction==0 then
      colorUnbindPending=false;colorLinkAction=1;colorLinkSamples=0;colorUidRequested=false
      if doBind() then status="Waiting RX link..." end
    elseif IS_COLOR and selected==ROW_UNBIND and target==TARGET_RX and colorLinkAction==0 and not colorUnbindPending and rxAlive() then
      colorUnbindPending=true;colorLinkAction=2;colorLinkSamples=0;colorUidRequested=false
      selected=ROW_BIND
      if doUnbind() then status="Waiting RX disconnect..." end
    elseif not IS_COLOR and selected==ROW_BIND and target==TARGET_RX and not rxAlive() then doBind()
    elseif not IS_COLOR and selected==ROW_UNBIND and target==TARGET_RX and rxAlive() then
      doUnbind()
    elseif IS_COLOR and selected==ROW_CLEAR then colorConfirm={armed=false}
    elseif IS_COLOR and selected>HIST_BASE+HISTORY_MAX then historyRemove(selected-HIST_BASE-HISTORY_MAX);selected=ROW_EXIT
    elseif IS_COLOR and selected>HIST_BASE then
      phrase=history[selected-HIST_BASE] or phrase;phraseEditor.value=phrase;status="History loaded";selected=ROW_PHRASE
    elseif selected==ROW_EXIT then exitRequested=true end
  elseif event==EVT_VIRTUAL_EXIT then exitRequested=true end
end

local function init()
  selected=1
  target=TARGET_TX
  historyLoad()
  phrase=history[1] or ""
  phraseEditor.value=phrase
  colorHistoryPage=false
  colorHistoryScroll=0
  colorHistoryScrollTarget=0
  colorUnbindPending=false
  colorLinkAction=0;colorLinkActionAt=0;colorLinkSamples=0;colorUidRequested=false
  colorFollowupPending=false
  bwPage=PAGE_MAIN
  bwFirst=1
  bothStep=nil;bothTxAttempts=0;bothPhrase=nil;bothRxWriteQueued=nil;bothTxWriteQueued=nil
  bwLastStatus=nil
  bwStatusAt=getTime()
  confirm=nil
  colorConfirm=nil
  uidFrom=nil
  uidReadDest=nil
  uidRequestActive=false
  uidLastRequestAt=nil
  uidQuarantineAt=nil
  rxSeen=false
  linkState=LINK_UNKNOWN;linkCandidate=nil;linkSamples=0;bindRefreshRx=false;uidTimeoutRecovery=false
  unbindIgnoreUp=false;unbindStartedAt=0
  elrsStatusSeen=false
  elrsStatusAt=0
  elrsStatusPollAt=-ELRS_STATUS_POLL
  status="Reading UID..."
  attempts=0
  cancel()
  edit=nil
  targetDropdown=false
  targetDropdownHeight=0
  targetDropdownTarget=0
  exitRequested=false
  schedule(1,"autoUid")
end
local function run(event,touchState)
  if event==nil then return 2 end
  drain();processTimer();requestElrsStatus()
  local alive=rxAlive()
  if target==TARGET_RX and alive and not lastRxAlive and attempts==0 and edit==nil and timer==nil then
    schedule(1,"autoUid")
  end
  lastRxAlive=alive
  if IS_COLOR and colorLinkAction~=0 then
    local timeout=(colorLinkAction==1) and COLOR_BIND_TIMEOUT or COLOR_UNBIND_TIMEOUT
    local now=getTime()
    if now-colorLinkActionAt>=timeout then
      local action=colorLinkAction
      colorLinkAction=0
      colorLinkActionAt=0
      colorUnbindPending=false
      colorUidRequested=false
      if action==2 then unbindIgnoreUp=false end
      if action==1 then
        bindRefreshRx=false
        status="Bind timed out"
      else
        local statusFresh=elrsStatusSeen and now-elrsStatusAt<ELRS_STATUS_TIMEOUT
        local stillConnected=statusFresh and rxSeen
        local disconnected=statusFresh and not rxSeen and linkState==LINK_DOWN
        linkState=stillConnected and LINK_UP or (disconnected and LINK_DOWN or LINK_UNKNOWN)
        linkCandidate=nil
        linkSamples=0
        status=stillConnected and "RX still connected" or (disconnected and "RX disconnected" or "Unbind timed out")
      end
    end
  end
  if IS_COLOR and colorLinkAction==2 and linkState==LINK_DOWN
      and elrsStatusSeen and getTime()-elrsStatusAt<ELRS_STATUS_TIMEOUT and not rxSeen then
    colorLinkSamples=0
    colorLinkAction=0
    colorLinkActionAt=0
    colorUnbindPending=false
    status="RX disconnected"
  end
  if IS_COLOR and colorConfirm then
    draw()
    local result=popupConfirmation("Clear all history?","PRESS [OK] to confirm",event)
    if not colorConfirm.armed then
      if event==0 then colorConfirm.armed=true end
      return 0
    end
    if result=="OK" then
      historyClear();selected=ROW_EXIT;colorConfirm=nil
    elseif result=="CANCEL" then
      selected=ROW_CLEAR;colorConfirm=nil
    end
    return 0
  end
  handle(event,touchState);draw()
  if exitRequested then return 2 end
  return 0
end
return {init=init,run=run}
