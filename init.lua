--[[
    spelldatagui - ImGui inspector for the MacroQuest `spell` datatype.

    This is the GUI version of the one-liner:
        /lua parse for i=1,255 do printf("%d %s", i, mq.TLO.Type("spell").Member(i)()) end

    Type a spell name (or a spell ID) and the window lists every member the `spell`
    datatype exposes, along with that spell's value for each member.
]]

---@type Mq
local mq = require('mq')
local ImGui = require('ImGui')
---@type spadata
local _SPAs = require('_SPAs')

local SCRIPT_NAME      = 'spelldatagui'
local WINDOW_TITLE     = 'Spell Data Inspector'
local MAX_MEMBER_INDEX = 255
local LOOKUP_DEBOUNCE  = 300
local AUTO_REFRESH_MS  = 1000
local MAX_DISPLAY_LEN  = 200
local COLOR_VALUE   = { 0.60, 0.95, 0.60, 1.00 }
local COLOR_NULL    = { 0.50, 0.62, 0.82, 1.00 }
local COLOR_ERROR   = { 0.55, 0.55, 0.55, 1.00 }
local COLOR_BAD     = { 1.00, 0.40, 0.40, 1.00 }
local COLOR_OK      = { 0.60, 0.95, 0.60, 1.00 }
local COLOR_HEADING = { 0.40, 0.85, 1.00, 1.00 }

local SNAPSHOT_YIELD_EVERY = 25
local SLOT_VALUE_MEMBERS = { 'Base', 'Base2', 'Max', 'Calc' }
local SPA_SLOT_MEMBERS   = { HasSPA = true, Attrib = true, Base = true, Base2 = true, Max = true, Calc = true }

---@class SpellEffectSlot
---@field slot integer
---@field spa integer
---@field spaName string|nil
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
---@field tloParam integer|nil

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

local openGUI, shouldDrawGUI = true, true

-- Member list cache (built once at startup, rebuildable via the Rescan button)
local membersByIndex = {}   -- { { index = n, name = 'Base' }, ... } sorted by index
local memberScanError = nil
---@type table<string, string>
local typeByMember = {}

-- Current lookup
local spellInput   = ''
local spellKey     = 0      -- what we pass to mq.TLO.Spell(...); 0 = no spell loaded
local spellName    = nil
local spellID      = nil
local statusText   = 'Enter a spell name or ID.'
local statusIsError = false

-- Value snapshot (rebuilt on lookup / refresh)
local rowsByIndex  = {}
local rowsByName   = {}
local countOK, countNull, countErr = 0, 0, 0
local lastRefresh  = 0

-- UI options
local memberFilter = ''
local sortAlpha    = false
local autoRefresh  = false

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
    return tostring(v), t
end

local function truncate(s)
    if #s > MAX_DISPLAY_LEN then
        return s:sub(1, MAX_DISPLAY_LEN) .. ' ...'
    end
    return s
end

local function copyToClipboard(text)
    ImGui.SetClipboardText(tostring(text))
end

-- ---------------------------------------------------------------------------
-- Member enumeration (the /lua parse one-liner, cached)
-- ---------------------------------------------------------------------------

local function scanMembers()
    local found = {}
    memberScanError = nil

    for i = 1, MAX_MEMBER_INDEX do
        local name = mq.TLO.Type('spell').Member(i)()
        -- Sparse index space: nils/blanks are holes, keep walking to MAX_MEMBER_INDEX.
        if name then
            name = trim(name)
            if name ~= '' and name ~= 'NULL' then
                found[#found + 1] = { index = i, name = name }
            end
        end
    end

    membersByIndex = found
    typeByMember = {}

    if #found == 0 then
        memberScanError = 'No members returned from Type[spell] -- the member lookup failed.'
    end
    printf('\ag[%s]\ax enumerated \ay%d\ax members of the spell datatype', SCRIPT_NAME, #found)
end

-- ---------------------------------------------------------------------------
-- Spell resolution + value snapshot
-- ---------------------------------------------------------------------------

--- Resolve the input as a spell name, or (if it's all digits) as an ID too.
---@param input string
---@return integer|nil spellID
local function resolveSpell(input)
    local text = trim(input)
    if text == '' then return nil end

    local candidates = { text }
    if text:match('^%d+$') then
        -- The Spell TLO takes name or ID, but try the numeric form explicitly too.
        candidates[#candidates + 1] = tonumber(text)
    end

    for _, key in ipairs(candidates) do
        local id = mq.TLO.Spell(key).ID()
        if id and id ~= 0 then
            return id
        end
    end
    return nil
end

--- True when the slot holds no effect: SPA_NOSPELL, or the SPA_CHA filler with a base of 0.
---@param key string|integer
---@param slot integer
---@param spa integer
---@return boolean
local function isEmptySlot(key, slot, spa)
    if spa == _SPAs.EQSPA.SPA_NOSPELL then return true end
    if spa ~= _SPAs.EQSPA.SPA_CHA then return false end
    return mq.TLO.Spell(key).Base(slot)() == 0
end

--- Read every non-empty effect slot on the spell: its SPA plus Base/Base2/Max/Calc.
---@param key string|integer
---@return SpellEffectSlot[]
local function readSpellEffects(key)
    local effects = {}
    local numEffects = mq.TLO.Spell(key).NumEffects()
    if not numEffects then return effects end

    for slot = 1, numEffects do
        local spa = mq.TLO.Spell(key).Attrib(slot)()
        if spa and not isEmptySlot(key, slot, spa) then
            local effect = { slot = slot, spa = spa, spaName = _SPAs.SPAName(spa), values = {} }
            for _, memberName in ipairs(SLOT_VALUE_MEMBERS) do
                effect.values[memberName] = formatValue(mq.TLO.Spell(key)[memberName](slot)())
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

--- MQ datatype name for a member, cached per member name once resolved.
---@param memberName string
---@return string|nil
local function memberType(memberName)
    local cached = typeByMember[memberName]
    if cached then return cached end
    local mqType = mq.gettype(mq.TLO.Spell(spellKey)[memberName])
    if mqType and trim(mqType) ~= '' then
        typeByMember[memberName] = mqType
        return mqType
    end
    return nil
end

--- Read one member of the current spell into a fresh display row.
---@param member SpellMember
---@param effects SpellEffectSlot[]
---@return SpellRow
local function buildRow(member, effects)
    local row = { index = member.index, name = member.name }

    if SPA_SLOT_MEMBERS[member.name] and #effects > 0 then
        local lines, summary = slotMemberLines(member.name, effects)
        row.state     = 'value'
        row.vtype     = member.name == 'HasSPA' and 'SPA list' or 'per slot'
        row.slotLines = lines
        row.tloParam  = member.name == 'HasSPA' and effects[1].spa or effects[1].slot
        row.copy      = table.concat(lines, '\n')
        row.display   = truncate(table.concat(summary, ', '))
        row.tooltip   = string.format('%s  [%s]\n\n%s', member.name, row.vtype, row.copy)
        return row
    end

    local ok, value = pcall(mq.TLO.Spell(spellKey)[member.name])
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
    row.vtype = memberType(member.name) or luaType
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
    row.tloParam  = fresh.tloParam
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

--- Read a fresh row for every member, yielding a frame every SNAPSHOT_YIELD_EVERY members.
---@param key integer
---@param members SpellMember[]
---@return SpellRow[]
local function readRows(key, members)
    local effects = readSpellEffects(key)
    local rows = {}
    for i, member in ipairs(members) do
        rows[i] = buildRow(member, effects)
        if i % SNAPSHOT_YIELD_EVERY == 0 then mq.delay(0) end
    end
    return rows
end

local function buildSnapshot()
    lastRefresh = mq.gettime()

    local key = spellKey
    if key == 0 then
        rowsByIndex, rowsByName = {}, {}
        countRows()
        return
    end

    local newByIndex = readRows(key, membersByIndex)
    local newByName = {}
    for i, row in ipairs(newByIndex) do newByName[i] = row end

    -- Same row tables, alternate ordering. Index is the stable tiebreak.
    table.sort(newByName, function(a, b)
        local an, bn = a.name:lower(), b.name:lower()
        if an == bn then return a.index < b.index end
        return an < bn
    end)

    rowsByIndex, rowsByName = newByIndex, newByName
    countRows()
end

--- Re-read the current spell's values, then update only rows whose value changed.
local function refreshSnapshot()
    if #rowsByIndex == 0 then
        buildSnapshot()
        return
    end

    lastRefresh = mq.gettime()
    local key = spellKey
    if key == 0 then return end

    local fresh = readRows(key, rowsByIndex)
    for i, row in ipairs(rowsByIndex) do
        applyRowChanges(row, fresh[i])
    end
    countRows()
end

local function clearResults()
    spellKey, spellName, spellID = 0, nil, nil
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

    local id = resolveSpell(text)
    if not id then
        clearResults()
        statusText    = string.format('No spell found for "%s"', text)
        statusIsError = true
        return
    end

    spellKey = id
    spellID  = id
    spellName = mq.TLO.Spell(id).Name() or text

    statusText    = string.format('%s (ID %d)', spellName, spellID)
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
    ImGui.SetNextItemWidth(260)
    local newInput, enterPressed = ImGui.InputText('Spell name or ID', spellInput, ImGuiInputTextFlags.EnterReturnsTrue)
    if newInput ~= spellInput then
        spellInput = newInput
        lookupDueAt = mq.gettime() + LOOKUP_DEBOUNCE
    end

    ImGui.SameLine()
    if ImGui.Button('Look up') or enterPressed then
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

    pushTextColor(statusIsError and COLOR_BAD or COLOR_OK)
    ImGui.TextUnformatted(statusText)
    ImGui.PopStyleColor()

    if memberScanError then
        pushTextColor(COLOR_BAD)
        ImGui.TextUnformatted(memberScanError)
        ImGui.PopStyleColor()
    end

    ImGui.Separator()

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
    if row.slotLines then
        local open = ImGui.TreeNode(row.display .. '###slots')
        if ImGui.IsItemHovered() then ImGui.SetTooltip('%s', row.tooltip) end
        if open then
            for _, line in ipairs(row.slotLines) do
                ImGui.TextUnformatted(line)
            end
            ImGui.TreePop()
        end
    else
        ImGui.TextUnformatted(row.display)
        if ImGui.IsItemHovered() then ImGui.SetTooltip('%s', row.tooltip) end
    end
    ImGui.PopStyleColor()

    ImGui.TableNextColumn()
    if ImGui.SmallButton('copy') then
        copyToClipboard(row.copy)
    end
    if ImGui.IsItemHovered() then ImGui.SetTooltip('Copy this value (right-click for more)') end
    if ImGui.BeginPopupContextItem('##copymenu') then
        if ImGui.MenuItem('Copy value') then copyToClipboard(row.copy) end
        if ImGui.MenuItem('Copy member name') then copyToClipboard(row.name) end
        if ImGui.MenuItem('Copy name = value') then
            copyToClipboard(string.format('%s = %s', row.name, row.copy))
        end
        if ImGui.MenuItem('Copy TLO expression') then
            if row.tloParam then
                copyToClipboard(string.format('mq.TLO.Spell(%d).%s(%d)()', spellID, row.name, row.tloParam))
            else
                copyToClipboard(string.format('mq.TLO.Spell(%d).%s()', spellID, row.name))
            end
        end
        ImGui.EndPopup()
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
        elseif spellKey ~= 0 then
            ImGui.TextDisabled('No member data -- try Refresh values.')
        else
            ImGui.TextDisabled('No spell loaded.')
        end
    end

    ImGui.End()
end

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

scanMembers()

mq.imgui.init(SCRIPT_NAME, drawGUI)
printf('\ag[%s]\ax running -- close the window to stop the script.', SCRIPT_NAME)

while openGUI do
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
    elseif autoRefresh and spellKey ~= 0 and (mq.gettime() - lastRefresh) >= AUTO_REFRESH_MS then
        refreshSnapshot()
    end

    mq.delay(100)
end

mq.imgui.destroy(SCRIPT_NAME)
printf('\ag[%s]\ax window closed, exiting.', SCRIPT_NAME)
