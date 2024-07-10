-- Arua Module
local arua = {}

local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local Workspace = game:GetService("Workspace")
local RunService = game:GetService("RunService")
local Debris = game:GetService("Debris")
local player = Players.LocalPlayer
local character
local punchEvent = ReplicatedStorage:WaitForChild("Remote Events"):WaitForChild("Punch")
local debounce = 0.4
local trackRange = 30
local punchRange = 20
local angleCheckEnabled = false
local visualizerEnabled = false
local animateEnabled = false
local stateCheckEnabled = false
local wallCheckEnabled = false
local aruaConnection
local lastPunchTime = 0
local visualizerPart

local punchAnimation = Instance.new("Animation")
punchAnimation.AnimationId = "rbxassetid://8266542505"

local function debugPrint(...)
    -- Debug printing enabled only for internal checks
    print(...)
end

local function isInFront(localPosition, localLookVector, targetPosition)
    local directionToTarget = (targetPosition - localPosition).Unit
    local dotProduct = localLookVector:Dot(directionToTarget)
    return dotProduct > 0.3
end

local function isRagdolled(targetCharacter)
    local ballSocketCount = 0
    local timeWindow = 1 -- Time window in seconds
    local lastBallSocketTime = 0

    local function checkForRagdoll()
        for _, part in ipairs(targetCharacter:GetDescendants()) do
            if part:IsA("BallSocketConstraint") then
                local currentTime = tick()
                if currentTime - lastBallSocketTime <= timeWindow then
                    ballSocketCount = ballSocketCount + 1
                else
                    ballSocketCount = 1
                end
                lastBallSocketTime = currentTime
                
                if ballSocketCount >= 6 then
                    return true
                end
            end
        end
        return false
    end

    return checkForRagdoll()
end

local function isBlockedByWall(localPosition, targetPosition)
    local ray = Ray.new(localPosition, (targetPosition - localPosition).Unit * (targetPosition - localPosition).Magnitude)
    local hitPart = Workspace:FindPartOnRay(ray, character)
    return hitPart and hitPart.CanCollide
end

local function trackPlayers()
    local trackedPlayers = {}
    local localRootPart = character and character:FindFirstChild("HumanoidRootPart")

    if not localRootPart then return {} end

    for _, targetPlayer in ipairs(Players:GetPlayers()) do
        if targetPlayer ~= player and targetPlayer.Character then
            local targetRootPart = targetPlayer.Character:FindFirstChild("HumanoidRootPart")
            if targetRootPart then
                local distance = (targetRootPart.Position - localRootPart.Position).Magnitude
                if distance <= trackRange and 
                (not angleCheckEnabled or isInFront(localRootPart.Position, localRootPart.CFrame.LookVector, targetRootPart.Position)) and 
                (not stateCheckEnabled or not isRagdolled(targetPlayer.Character)) and 
                (not wallCheckEnabled or not isBlockedByWall(localRootPart.Position, targetRootPart.Position)) then
                    trackedPlayers[targetPlayer] = distance
                end
            end
        end
    end

    return trackedPlayers
end

local function getNearestTrackedPlayer(trackedPlayers)
    local closestPlayer
    local shortestDistance = math.huge
    for targetPlayer, distance in pairs(trackedPlayers) do
        if distance <= punchRange and distance < shortestDistance then
            closestPlayer = targetPlayer
            shortestDistance = distance
        end
    end
    return closestPlayer
end

local function createVisualizerPart(targetModel)
    local humanoidRootPart = targetModel:FindFirstChild("HumanoidRootPart")
    if not humanoidRootPart then return end

    if visualizerPart then visualizerPart:Destroy() end

    visualizerPart = Instance.new("Part")
    visualizerPart.Name = "Visualizer"
    visualizerPart.Size = Vector3.new(4, 6, 4)
    visualizerPart.Transparency = 0.5
    visualizerPart.Anchored = true
    visualizerPart.CanCollide = false
    visualizerPart.Color = Color3.new(1, 0, 0)
    visualizerPart.Material = Enum.Material.ForceField
    visualizerPart.CFrame = humanoidRootPart.CFrame
    visualizerPart.Parent = Workspace

    Debris:AddItem(visualizerPart, 1)
end

local function punchNearestPlayer(trackedPlayers)
    local currentTime = tick()
    if currentTime - lastPunchTime < debounce then return end
    lastPunchTime = currentTime

    local nearestPlayer = getNearestTrackedPlayer(trackedPlayers)
    if nearestPlayer and nearestPlayer.Character then
        local targetRootPart = nearestPlayer.Character:FindFirstChild("HumanoidRootPart")
        if targetRootPart then
            punchEvent:FireServer(nearestPlayer.Character, targetRootPart.Position + Vector3.new(0, 0.5, 0), (character.HumanoidRootPart.Position - targetRootPart.Position).Magnitude, targetRootPart)

            if visualizerEnabled then
                createVisualizerPart(nearestPlayer.Character)
            end

            if animateEnabled then
                local humanoid = character:FindFirstChild("Humanoid")
                if humanoid then
                    local animationTrack = humanoid:LoadAnimation(punchAnimation)
                    animationTrack:Play()
                end
            end
        end
    end
end

local function onCharacterAdded(newCharacter)
    character = newCharacter
end

function arua.start()
    if aruaConnection then return end
    player.CharacterAdded:Connect(onCharacterAdded)
    character = player.Character or player.CharacterAdded:Wait()
    aruaConnection = RunService.Stepped:Connect(function()
        local trackedPlayers = trackPlayers()
        punchNearestPlayer(trackedPlayers)
    end)
    debugPrint("[Debug] Arua module started.")
end

function arua.stop()
    if aruaConnection then
        aruaConnection:Disconnect()
        aruaConnection = nil
    end
    debugPrint("[Debug] Arua module stopped.")
end

function arua.updateRange(value)
    punchRange = tonumber(value) or 20
    debugPrint("[Debug] Punch range updated to:", punchRange)
end

function arua.toggleAngleCheck(callback)
    angleCheckEnabled = callback
    debugPrint("[Debug] Angle check toggled:", callback)
end

function arua.toggleVisualizer(callback)
    visualizerEnabled = callback
    debugPrint("[Debug] Visualizer toggled:", callback)
end

function arua.toggleAnimate(callback)
    animateEnabled = callback
    debugPrint("[Debug] Animate toggled:", callback)
end

function arua.toggleStateCheck(callback)
    stateCheckEnabled = callback
    debugPrint("[Debug] State check toggled:", callback)
end

function arua.toggleWallCheck(callback)
    wallCheckEnabled = callback
    debugPrint("[Debug] Wall check toggled:", callback)
end

return arua
