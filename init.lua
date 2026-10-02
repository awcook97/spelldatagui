--[[
    spelldatagui - ImGui inspector for the MacroQuest `spell` datatype.

    This is the GUI version of the one-liner:
        /lua parse for i=1,255 do printf("%d %s", i, mq.TLO.Type("spell").Member(i)()) end

    Type a spell name (or a spell ID) and the window lists every member the `spell`
    datatype exposes, along with that spell's value for each member.

    ---------------------------------------------------------------------------
    NOTES
    ---------------------------------------------------------------------------
    * Type[spell].Member[N] is documented as "not all values will be used", so the
      index space is sparse -- we skip holes rather than stopping at the first nil.
    * Plenty of spell members require an index/param: Base(n), Attrib(n), Trigger(n),
      StacksWith(...), etc. Reading those bare raises a Lua error out of the MQ
      binding, so EVERY read here is pcall-wrapped and failures render dimmed as
      <requires param> with the real error in the tooltip.
    * All TLO reads happen in the main loop, never inside the ImGui draw callback.
      A full snapshot is ~2 evaluations x ~150 members; doing that every frame would
      stutter the client.
]]

---@type Mq
local mq = require('mq')
local ImGui = require('ImGui')
local _SPAs = require('_SPAs')

local SCRIPT_NAME      = 'spelldatagui'
local WINDOW_TITLE     = 'Spell Data Inspector'
local MAX_MEMBER_INDEX = 255   -- Type[spell].Member[N] is 1..N, sparse
local LOOKUP_DEBOUNCE  = 300   -- ms to wait after typing before re-reading
local AUTO_REFRESH_MS  = 1000  -- how often auto-refresh re-snapshots values
local MAX_DISPLAY_LEN  = 200   -- truncate long values in the table (tooltip has all)

-- Colors (r, g, b, a)
local COLOR_VALUE   = { 0.60, 0.95, 0.60, 1.00 }  -- real value
local COLOR_NULL    = { 0.50, 0.62, 0.82, 1.00 }  -- member resolved but was NULL
local COLOR_ERROR   = { 0.55, 0.55, 0.55, 1.00 }  -- threw / needs a param
local COLOR_BAD     = { 1.00, 0.40, 0.40, 1.00 }  -- status line errors
local COLOR_OK      = { 0.60, 0.95, 0.60, 1.00 }
local COLOR_HEADING = { 0.40, 0.85, 1.00, 1.00 }

local SPA_NOSPELL        = _SPAs.EQSPA.SPA_NOSPELL
local SPA_CHA            = _SPAs.EQSPA.SPA_CHA
local SLOT_VALUE_MEMBERS = { 'Base', 'Base2', 'Max', 'Calc' }
local SPA_SLOT_MEMBERS   = { HasSPA = true, Attrib = true, Base = true, Base2 = true, Max = true, Calc = true }

---@class SpellEffectSlot
---@field slot integer
---@field spa integer
---@field spaName string
---@field values table<string, string>

---@class SpellMember
---@field index integer
---@field name string

---@class SpellRow: SpellMember
---@field state 'value'|'null'|'error'
---@field vtype string
---@field display string
---@field copy string
---@field tooltip string
---@field slotLines string[]|nil

-- Optional bindings -- guard so the script still runs on older MQ builds.
local hasGetType   = type(mq.gettype) == 'function'
local hasClipboard = type(ImGui.SetClipboardText) == 'function'

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

local openGUI, shouldDrawGUI = true, true

-- Member list cache (built once at startup, rebuildable via the Rescan button)
local membersByIndex = {}   -- { { index = n, name = 'Base' }, ... } sorted by index
local memberScanError = nil

-- Current lookup
local spellInput   = ''     -- raw text in the InputText
local spellKey     = nil    -- what we actually pass to mq.TLO.Spell(...)
local spellName    = nil
local spellID      = nil
local statusText   = 'Enter a spell name or ID.'
local statusIsError = false

-- Value snapshot (rebuilt on lookup / refresh)
local rowsByIndex  = {}     -- ordered by member index
local rowsByName   = {}     -- same row tables, ordered alphabetically
local countOK, countNull, countErr = 0, 0, 0
local lastRefresh  = 0

-- UI options
local memberFilter = ''
local sortAlpha    = false
local autoRefresh  = false

-- Work requests from the draw callback -> main loop
local pendingRescan  = false
local pendingLookup  = false
local pendingRefresh = false
local lookupDueAt    = nil

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

local function trim(s)
    return (tostring(s or ''):match('^%s*(.-)%s*$'))
end

--- Strip the "file.lua:123: " prefix and newlines off a Lua/sol error.
local function cleanError(err)
    local s = tostring(err or 'unknown error')
    s = s:gsub('^.-%.lua:%d+:%s*', '')
    s = s:gsub('^.-:%d+:%s*', '')
    s = s:gsub('%s+', ' ')
    return trim(s)
end

--- Errors that look like "this member needs an index" get the friendly marker.
local function isParamError(msg)
    local lower = msg:lower()
    return lower:find('evaluate member', 1, true) ~= nil
        or lower:find('failed to evaluate', 1, true) ~= nil
        or lower:find('no member', 1, true) ~= nil
end

--- Coerce any Lua value coming back from a TLO into something printable.
--- Returns displayText, luaTypeName.
local function formatValue(v)
    local t = type(v)
    if v == nil then
        return 'NULL', 'nil'
    elseif t == 'number' then
        -- Keep whole numbers looking like ints instead of 1.0
        if v == math.floor(v) and math.abs(v) < 2 ^ 53 then
            return string.format('%d', v), 'number'
        end
        return string.format('%.4f', v), 'number'
    elseif t == 'string' then
        return v, 'string'
    elseif t == 'boolean' then
        return tostring(v), 'boolean'
    end
    -- userdata / table / function: tostring can itself throw on MQ userdata
    local ok, s = pcall(tostring, v)
    return (ok and s or ('<un-tostring-able ' .. t .. '>')), t
end

local function truncate(s)
    if #s > MAX_DISPLAY_LEN then
        return s:sub(1, MAX_DISPLAY_LEN) .. ' ...'
    end
    return s
end

local function copyToClipboard(text)
    if hasClipboard then
        ImGui.SetClipboardText(tostring(text))
    end
end

-- ---------------------------------------------------------------------------
-- Member enumeration (the /lua parse one-liner, cached)
-- ---------------------------------------------------------------------------

--- Pulled out so pcall doesn't need a fresh closure per iteration.
local function readMemberName(i)
    return mq.TLO.Type('spell').Member(i)()
end

local function scanMembers()
    local found = {}
    memberScanError = nil

    for i = 1, MAX_MEMBER_INDEX do
        local ok, name = pcall(readMemberName, i)
        -- Sparse index space: nils/blanks are holes, keep walking to MAX_MEMBER_INDEX.
        if ok and type(name) == 'string' then
            name = trim(name)
            if name ~= '' and name ~= 'NULL' then
                found[#found + 1] = { index = i, name = name }
            end
        end
    end

    table.sort(found, function(a, b) return a.index < b.index end)
    membersByIndex = found

    if #found == 0 then
        memberScanError = 'No members returned from Type[spell] -- are you in game?'
    end
    printf('\ag[%s]\ax enumerated \ay%d\ax members of the spell datatype', SCRIPT_NAME, #found)
end

-- ---------------------------------------------------------------------------
-- Spell resolution + value snapshot
-- ---------------------------------------------------------------------------

local function readSpellID(key)
    return mq.TLO.Spell(key).ID()
end

local function readSpellName(key)
    return mq.TLO.Spell(key).Name()
end

--- Try the input as a name, and (if it's all digits) as an ID too.
--- Returns the key that resolved plus the spell ID, or nil.
local function resolveSpell(input)
    local text = trim(input)
    if text == '' then return nil end

    local candidates = { text }
    if text:match('^%d+$') then
        -- The Spell TLO takes name or ID, but try the numeric form explicitly too.
        candidates[#candidates + 1] = tonumber(text)
    end

    for _, key in ipairs(candidates) do
        local ok, id = pcall(readSpellID, key)
        if ok and id and id ~= 0 then
            return key, id
        end
    end
    return nil
end

--- Read one member off the spell. Separate function so pcall gets a plain call.
--- NOTE: spell[memberName] is the dynamic form of spell.MemberName -- in Lua both
--- go through the same __index metamethod on the MQ typevar userdata.
local function readMemberValue(key, memberName)
    return mq.TLO.Spell(key)[memberName]()
end

--- Grab the MQ datatype name of a member by handing the *unevaluated* proxy to
--- mq.gettype. This evaluates the member again, so it can throw just like the
--- value read can -- caller pcalls it.
local function readMemberType(key, memberName)
    return mq.gettype(mq.TLO.Spell(key)[memberName])
end

--- Read a slot-indexed member such as Attrib(slot).
local function readSlotValue(key, memberName, slot)
    return mq.TLO.Spell(key)[memberName](slot)()
end

--- True when the slot holds no effect: SPA_NOSPELL, or the SPA_CHA filler with a base of 0.
---@param key string|integer
---@param slot integer
---@param spa integer
---@return boolean
local function isEmptySlot(key, slot, spa)
    if spa == SPA_NOSPELL then return true end
    if spa ~= SPA_CHA then return false end
    local okBase, base = pcall(readSlotValue, key, 'Base', slot)
    return okBase and base == 0
end

--- Read every non-empty effect slot on the spell: its SPA plus Base/Base2/Max/Calc.
---@param key string|integer
---@return SpellEffectSlot[]
local function readSpellEffects(key)
    local effects = {}
    local okCount, numEffects = pcall(readMemberValue, key, 'NumEffects')
    if not okCount or type(numEffects) ~= 'number' then return effects end

    for slot = 1, numEffects do
        local okSpa, spa = pcall(readSlotValue, key, 'Attrib', slot)
        if okSpa and type(spa) == 'number' and not isEmptySlot(key, slot, spa) then
            local effect = { slot = slot, spa = spa, spaName = _SPAs.SPAName(spa) or 'unknown SPA', values = {} }
            for _, memberName in ipairs(SLOT_VALUE_MEMBERS) do
                local okValue, value = pcall(readSlotValue, key, memberName, slot)
                effect.values[memberName] = okValue and (formatValue(value)) or '?'
            end
            effects[#effects + 1] = effect
        end
    end
    return effects
end

--- Detail lines and short summary values for an SPA-related member across the spell's effect slots.
---@param memberName string
---@param effects SpellEffectSlot[]
---@return string[] lines
---@return string[] summary
local function slotMemberLines(memberName, effects)
    local lines, summary, seen = {}, {}, {}
    for _, effect in ipairs(effects) do
        if memberName == 'HasSPA' then
            if not seen[effect.spa] then
                seen[effect.spa] = true
                lines[#lines + 1] = string.format('%s (%d)', effect.spaName, effect.spa)
                summary[#summary + 1] = effect.spaName
            end
        elseif memberName == 'Attrib' then
            lines[#lines + 1] = string.format('slot %d: %s (%d)', effect.slot, effect.spaName, effect.spa)
            summary[#summary + 1] = tostring(effect.spa)
        else
            local value = effect.values[memberName]
            lines[#lines + 1] = string.format('slot %d: %s  [%s]', effect.slot, value, effect.spaName)
            summary[#summary + 1] = value
        end
    end
    return lines, summary
end

--- Read one member of the current spell into a fresh display row.
---@param member SpellMember
---@param effects SpellEffectSlot[]
---@param knownType string|nil MQ type already resolved for this member; skips mq.gettype
---@return SpellRow
local function buildRow(member, effects, knownType)
    local row = { index = member.index, name = member.name }

    if SPA_SLOT_MEMBERS[member.name] and #effects > 0 then
        local lines, summary = slotMemberLines(member.name, effects)
        row.state     = 'value'
        row.vtype     = member.name == 'HasSPA' and 'SPA list' or 'per slot'
        row.slotLines = lines
        row.copy      = table.concat(lines, '\n')
        row.display   = truncate(table.concat(summary, ', '))
        row.tooltip   = string.format('%s  [%s]\n\n%s', member.name, row.vtype, row.copy)
        return row
    end

    local ok, value = pcall(readMemberValue, spellKey, member.name)
    if not ok then
        local msg = cleanError(value)
        row.state   = 'error'
        row.vtype   = '--'
        row.display = isParamError(msg) and '<requires param>' or ('<error> ' .. truncate(msg))
        row.copy    = msg
        row.tooltip = string.format('%s\n\n%s', member.name, msg)
        return row
    end

    local text, luaType = formatValue(value)
    row.state = (value == nil) and 'null' or 'value'
    row.vtype = knownType or luaType

    if not knownType and hasGetType then
        local okType, mqType = pcall(readMemberType, spellKey, member.name)
        if okType and type(mqType) == 'string' and trim(mqType) ~= '' then
            row.vtype = mqType
        end
    end

    row.copy    = text
    row.display = truncate(text)
    row.tooltip = string.format('%s  [%s]\n\n%s', member.name, row.vtype, text)
    return row
end

--- Copy a freshly read row onto the displayed row, only when its value, state or type changed.
---@param row SpellRow
---@param fresh SpellRow
local function applyRowChanges(row, fresh)
    if row.copy == fresh.copy and row.state == fresh.state and row.vtype == fresh.vtype then return end
    row.state     = fresh.state
    row.vtype     = fresh.vtype
    row.display   = fresh.display
    row.copy      = fresh.copy
    row.tooltip   = fresh.tooltip
    row.slotLines = fresh.slotLines
end

--- Recompute the value / null / error counts from the current rows.
local function countRows()
    countOK, countNull, countErr = 0, 0, 0
    for _, row in ipairs(rowsByIndex) do
        if row.state == 'error' then
            countErr = countErr + 1
        elseif row.state == 'null' then
            countNull = countNull + 1
        else
            countOK = countOK + 1
        end
    end
end

local function buildSnapshot()
    rowsByIndex, rowsByName = {}, {}
    lastRefresh = mq.gettime()

    if not spellKey then
        countRows()
        return
    end

    local effects = readSpellEffects(spellKey)

    for _, member in ipairs(membersByIndex) do
        local row = buildRow(member, effects)
        rowsByIndex[#rowsByIndex + 1] = row
        rowsByName[#rowsByName + 1]   = row
    end
    countRows()

    -- Same row tables, alternate ordering. Index is the stable tiebreak.
    table.sort(rowsByName, function(a, b)
        local an, bn = a.name:lower(), b.name:lower()
        if an == bn then return a.index < b.index end
        return an < bn
    end)
end

--- Re-read the current spell's values in place, updating only rows whose value changed.
local function refreshSnapshot()
    if #rowsByIndex == 0 then
        buildSnapshot()
        return
    end

    lastRefresh = mq.gettime()
    if not spellKey then return end

    local effects = readSpellEffects(spellKey)
    for _, row in ipairs(rowsByIndex) do
        local knownType = row.state ~= 'error' and row.vtype or nil
        applyRowChanges(row, buildRow(row, effects, knownType))
    end
    countRows()
end

local function clearResults()
    spellKey, spellName, spellID = nil, nil, nil
    rowsByIndex, rowsByName = {}, {}
    countOK, countNull, countErr = 0, 0, 0
end

local function doLookup()
    local text = trim(spellInput)
    if text == '' then
        clearResults()
        statusText, statusIsError = 'Enter a spell name or ID.', false
        return
    end

    local key, id = resolveSpell(text)
    if not key then
        clearResults()
        statusText    = string.format('No spell found for "%s"', text)
        statusIsError = true
        return
    end

    spellKey = key
    spellID  = id
    local okName, name = pcall(readSpellName, key)
    spellName = (okName and name) or text

    statusText    = string.format('%s (ID %d)', tostring(spellName), tonumber(spellID) or 0)
    statusIsError = false
    buildSnapshot()
end

-- ---------------------------------------------------------------------------
-- ImGui
-- ---------------------------------------------------------------------------

local TABLE_FLAGS = bit32.bor(
    ImGuiTableFlags.Resizable,
    ImGuiTableFlags.Reorderable,
    ImGuiTableFlags.Hideable,
    ImGuiTableFlags.RowBg,
    ImGuiTableFlags.BordersOuter,
    ImGuiTableFlags.BordersV,
    ImGuiTableFlags.NoBordersInBody,
    ImGuiTableFlags.ScrollY
)

local function pushStateColor(state)
    local c = COLOR_VALUE
    if state == 'error' then c = COLOR_ERROR
    elseif state == 'null' then c = COLOR_NULL end
    ImGui.PushStyleColor(ImGuiCol.Text, c[1], c[2], c[3], c[4])
end

local function pushTextColor(c)
    ImGui.PushStyleColor(ImGuiCol.Text, c[1], c[2], c[3], c[4])
end

local function drawToolbar()
    -- Spell input --------------------------------------------------------
    ImGui.SetNextItemWidth(260)
    local newInput, inputChanged = ImGui.InputText('Spell name or ID', spellInput)
    if inputChanged then
        spellInput = newInput
        lookupDueAt = mq.gettime() + LOOKUP_DEBOUNCE
    end

    ImGui.SameLine()
    if ImGui.Button('Look up') then
        lookupDueAt = nil
        pendingLookup = true
    end

    ImGui.SameLine()
    if ImGui.Button('Refresh values') then
        pendingRefresh = true
    end

    ImGui.SameLine()
    if ImGui.Button('Rescan members') then
        pendingRescan = true
    end

    -- Status -------------------------------------------------------------
    pushTextColor(statusIsError and COLOR_BAD or COLOR_OK)
    ImGui.TextUnformatted(statusText)
    ImGui.PopStyleColor()

    if memberScanError then
        pushTextColor(COLOR_BAD)
        ImGui.TextUnformatted(memberScanError)
        ImGui.PopStyleColor()
    end

    ImGui.Separator()

    -- Filter + options ---------------------------------------------------
    ImGui.SetNextItemWidth(200)
    memberFilter = ImGui.InputText('Filter members', memberFilter)

    ImGui.SameLine()
    if ImGui.Button('Clear##filter') then memberFilter = '' end

    ImGui.SameLine()
    if ImGui.RadioButton('By index', not sortAlpha) then sortAlpha = false end
    ImGui.SameLine()
    if ImGui.RadioButton('Alphabetical', sortAlpha) then sortAlpha = true end

    ImGui.SameLine()
    autoRefresh = ImGui.Checkbox('Auto-refresh', autoRefresh)

    -- Counts -------------------------------------------------------------
    pushTextColor(COLOR_HEADING)
    ImGui.TextUnformatted(string.format(
        '%d members | %d values | %d null | %d need a param / errored',
        #membersByIndex, countOK, countNull, countErr))
    ImGui.PopStyleColor()
end

local function drawRow(row)
    ImGui.PushID(row.index)

    ImGui.TableNextColumn()
    ImGui.TextUnformatted(tostring(row.index))

    ImGui.TableNextColumn()
    ImGui.TextUnformatted(row.name)
    if ImGui.IsItemHovered() then ImGui.SetTooltip('%s', row.tooltip) end

    ImGui.TableNextColumn()
    ImGui.TextDisabled('%s', row.vtype)

    ImGui.TableNextColumn()
    pushStateColor(row.state)
    -- TextUnformatted, not Text: ImGui.Text treats arg 1 as a format string and
    -- spell values (e.g. "Increase Hitpoints by 100%") contain % signs.
    if row.slotLines then
        if ImGui.TreeNode(row.display .. '##slots') then
            for _, line in ipairs(row.slotLines) do
                ImGui.TextUnformatted(line)
            end
            ImGui.TreePop()
        end
    else
        ImGui.TextUnformatted(row.display)
    end
    ImGui.PopStyleColor()
    if ImGui.IsItemHovered() then ImGui.SetTooltip('%s', row.tooltip) end

    ImGui.TableNextColumn()
    if hasClipboard then
        if ImGui.SmallButton('copy') then
            copyToClipboard(row.copy)
        end
        if ImGui.IsItemHovered() then ImGui.SetTooltip('Copy this value (right-click for more)') end
        -- Right-click the copy button for the other copy flavors.
        if ImGui.BeginPopupContextItem('##copymenu') then
            if ImGui.MenuItem('Copy value') then copyToClipboard(row.copy) end
            if ImGui.MenuItem('Copy member name') then copyToClipboard(row.name) end
            if ImGui.MenuItem('Copy name = value') then
                copyToClipboard(string.format('%s = %s', row.name, row.copy))
            end
            if ImGui.MenuItem('Copy TLO expression') then
                copyToClipboard(string.format('mq.TLO.Spell(%q).%s()', tostring(spellName), row.name))
            end
            ImGui.EndPopup()
        end
    else
        ImGui.TextDisabled('n/a')
    end

    ImGui.PopID()
end

local function drawTable()
    local rows = sortAlpha and rowsByName or rowsByIndex
    local filter = memberFilter:lower()

    local _, availY = ImGui.GetContentRegionAvail()
    if not availY or availY < 60 then availY = 60 end

    if not ImGui.BeginTable('##spellmembers', 5, TABLE_FLAGS, 0.0, availY, 0.0) then
        return
    end

    ImGui.TableSetupColumn('#', ImGuiTableColumnFlags.WidthFixed, 40.0)
    ImGui.TableSetupColumn('Member', ImGuiTableColumnFlags.WidthFixed, 190.0)
    ImGui.TableSetupColumn('Type', ImGuiTableColumnFlags.WidthFixed, 90.0)
    ImGui.TableSetupColumn('Value', ImGuiTableColumnFlags.WidthStretch)
    ImGui.TableSetupColumn('Copy', ImGuiTableColumnFlags.WidthFixed, 48.0)
    ImGui.TableSetupScrollFreeze(0, 1)
    ImGui.TableHeadersRow()

    for _, row in ipairs(rows) do
        if filter == '' or row.name:lower():find(filter, 1, true) then
            ImGui.TableNextRow()
            drawRow(row)
        end
    end

    ImGui.EndTable()
end

local function drawGUI()
    ImGui.SetNextWindowSize(760, 520, ImGuiCond.FirstUseEver)
    openGUI, shouldDrawGUI = ImGui.Begin(WINDOW_TITLE, openGUI)

    if shouldDrawGUI then
        drawToolbar()
        if #rowsByIndex > 0 then
            drawTable()
        elseif spellKey then
            ImGui.TextDisabled('No member data -- try Refresh values.')
        else
            ImGui.TextDisabled('No spell loaded.')
        end
    end

    -- Begin/End are the odd pair: End() must be called regardless of the return.
    ImGui.End()
end

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

scanMembers()

mq.imgui.init(SCRIPT_NAME, drawGUI)
printf('\ag[%s]\ax running -- close the window to stop the script.', SCRIPT_NAME)

while openGUI do
    -- All TLO work happens here, never in the draw callback.
    if pendingRescan then
        pendingRescan = false
        pendingRefresh = false
        scanMembers()
        buildSnapshot()
    end

    if lookupDueAt and mq.gettime() >= lookupDueAt then
        lookupDueAt = nil
        pendingLookup = true
    end

    if pendingLookup then
        pendingLookup = false
        pendingRefresh = false
        doLookup()
    elseif pendingRefresh then
        pendingRefresh = false
        refreshSnapshot()
    elseif autoRefresh and spellKey and (mq.gettime() - lastRefresh) >= AUTO_REFRESH_MS then
        refreshSnapshot()
    end

    mq.delay(100)
end

mq.imgui.destroy(SCRIPT_NAME)
printf('\ag[%s]\ax window closed, exiting.', SCRIPT_NAME)
