--[[
════════════════════════════════════════════════════════════════
    🔥 KAKA HUB V4 - VERSÃO FINAL COMPLETA 🔥
    Discord: https://discord.gg/uPU8Xwa64c
    Link Key: https://direct-link.net/3181536/5L523TZ84xtQ
    GitHub: https://carlitus777.github.io/kaka-hub-keys/
    
    ✨ SISTEMA COMPLETO:
    - Keys geradas automaticamente
    - Verificação de formato (KAKA-DDMMYYYY-XXXXXX)
    - Auto save com expiração 24h
    - ESP desativado por padrão
    - Auto Teleport
    - Detecção inteligente de 3 dedos
════════════════════════════════════════════════════════════════
]]--

print("🔥 KAKA HUB V4 FINAL inicializando...")

local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local Players = game:GetService("Players")
local CoreGui = game:GetService("CoreGui")
local LocalPlayer = Players.LocalPlayer

local KEY_CONFIG = {
    DiscordLink = "https://discord.gg/uPU8Xwa64c",
    KeyLink = "https://direct-link.net/3181536/5L523TZ84xtQ",
    GitHubPage = "https://carlitus777.github.io/kaka-hub-keys/"
}

local COLORS = {
    Background = Color3.fromRGB(20, 20, 30),
    Secondary = Color3.fromRGB(30, 30, 45),
    Primary = Color3.fromRGB(138, 43, 226),
    PrimaryDark = Color3.fromRGB(100, 30, 180),
    Accent = Color3.fromRGB(186, 85, 211),
    KeyButton = Color3.fromRGB(46, 204, 113),
    Text = Color3.fromRGB(255, 255, 255),
    TextDim = Color3.fromRGB(200, 200, 200),
    Success = Color3.fromRGB(46, 204, 113),
    Error = Color3.fromRGB(231, 76, 60),
}

local SavedKeyFile = "KakaHubV4_SavedKey.json"

local function SaveKey(key)
    local keyData = {key = key, timestamp = os.time()}
    writefile(SavedKeyFile, game:GetService("HttpService"):JSONEncode(keyData))
end

local function LoadSavedKey()
    if isfile(SavedKeyFile) then
        local success, data = pcall(function()
            return game:GetService("HttpService"):JSONDecode(readfile(SavedKeyFile))
        end)
        if success and data then
            if os.time() - data.timestamp < 86400 then
                return data.key
            else
                delfile(SavedKeyFile)
            end
        end
    end
    return nil
end

local function VerifyKey(key)
    if not key or type(key) ~= "string" then return false end
    key = key:gsub("^%s*(.-)%s*$", "%1")
    
    local parts = {}
    for part in key:gmatch("[^-]+") do table.insert(parts, part) end
    
    if #parts ~= 3 then return false end
    if parts[1] ~= "KAKA" then return false end
    if not parts[2]:match("^%d%d%d%d%d%d%d%d$") then return false end
    if not parts[3]:match("^%w%w%w%w%w%w$") then return false end
    
    local keyDate = parts[2]
    local today = os.date("%d%m%Y")
    local yesterday = os.date("%d%m%Y", os.time() - 86400)
    
    return keyDate == today or keyDate == yesterday
end

local function Tween(object, goal, duration, style, direction)
    return TweenService:Create(object, TweenInfo.new(duration or 0.3, style or Enum.EasingStyle.Quad, direction or Enum.EasingDirection.Out), goal):Play()
end

local function CreateKeySystem()
    local ScreenGui = Instance.new("ScreenGui")
    ScreenGui.Name = "KakaKeySystem"
    ScreenGui.ResetOnSpawn = false
    ScreenGui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
    ScreenGui.IgnoreGuiInset = true
    
    local BlurFrame = Instance.new("Frame")
    BlurFrame.Size = UDim2.new(1, 0, 1, 0)
    BlurFrame.BackgroundColor3 = Color3.fromRGB(0, 0, 0)
    BlurFrame.BackgroundTransparency = 0.3
    BlurFrame.BorderSizePixel = 0
    BlurFrame.Parent = ScreenGui
    
    local MainContainer = Instance.new("Frame")
    MainContainer.Size = UDim2.new(0, 500, 0, 420)
    MainContainer.Position = UDim2.new(0.5, -250, 0.5, -210)
    MainContainer.BackgroundColor3 = COLORS.Background
    MainContainer.BorderSizePixel = 0
    MainContainer.Parent = ScreenGui
    Instance.new("UICorner", MainContainer).CornerRadius = UDim.new(0, 15)
    
    local TopBar = Instance.new("Frame")
    TopBar.Size = UDim2.new(1, 0, 0, 60)
    TopBar.BackgroundColor3 = COLORS.Primary
    TopBar.BorderSizePixel = 0
    TopBar.Parent = MainContainer
    Instance.new("UICorner", TopBar).CornerRadius = UDim.new(0, 15)
    
    local TopFill = Instance.new("Frame")
    TopFill.Size = UDim2.new(1, 0, 0, 30)
    TopFill.Position = UDim2.new(0, 0, 1, -30)
    TopFill.BackgroundColor3 = COLORS.Primary
    TopFill.BorderSizePixel = 0
    TopFill.Parent = TopBar
    
    local Title = Instance.new("TextLabel")
    Title.Size = UDim2.new(1, -100, 1, 0)
    Title.Position = UDim2.new(0, 70, 0, 0)
    Title.BackgroundTransparency = 1
    Title.Text = "🔑 KAKA HUB V4"
    Title.TextColor3 = COLORS.Text
    Title.Font = Enum.Font.GothamBold
    Title.TextSize = 22
    Title.TextXAlignment = Enum.TextXAlignment.Left
    Title.Parent = TopBar
    
    local CloseButton = Instance.new("TextButton")
    CloseButton.Size = UDim2.new(0, 40, 0, 40)
    CloseButton.Position = UDim2.new(1, -50, 0, 10)
    CloseButton.BackgroundColor3 = COLORS.Error
    CloseButton.Text = "✕"
    CloseButton.TextColor3 = COLORS.Text
    CloseButton.Font = Enum.Font.GothamBold
    CloseButton.TextSize = 20
    CloseButton.Parent = TopBar
    Instance.new("UICorner", CloseButton).CornerRadius = UDim.new(0, 10)
    
    local Content = Instance.new("Frame")
    Content.Size = UDim2.new(1, -50, 1, -110)
    Content.Position = UDim2.new(0, 25, 0, 75)
    Content.BackgroundTransparency = 1
    Content.Parent = MainContainer
    
    local Description = Instance.new("TextLabel")
    Description.Size = UDim2.new(1, 0, 0, 70)
    Description.BackgroundTransparency = 1
    Description.Text = "🔐 Digite sua chave de acesso\n\nPegue sua key nos botões abaixo"
    Description.TextColor3 = COLORS.TextDim
    Description.Font = Enum.Font.Gotham
    Description.TextSize = 14
    Description.TextWrapped = true
    Description.Parent = Content
    
    local InputFrame = Instance.new("Frame")
    InputFrame.Size = UDim2.new(1, 0, 0, 50)
    InputFrame.Position = UDim2.new(0, 0, 0, 85)
    InputFrame.BackgroundColor3 = COLORS.Secondary
    InputFrame.BorderSizePixel = 0
    InputFrame.Parent = Content
    Instance.new("UICorner", InputFrame).CornerRadius = UDim.new(0, 10)
    
    local KeyInput = Instance.new("TextBox")
    KeyInput.Size = UDim2.new(1, -50, 1, 0)
    KeyInput.Position = UDim2.new(0, 45, 0, 0)
    KeyInput.BackgroundTransparency = 1
    KeyInput.PlaceholderText = "Cole a key aqui..."
    KeyInput.PlaceholderColor3 = COLORS.TextDim
    KeyInput.Text = ""
    KeyInput.TextColor3 = COLORS.Text
    KeyInput.Font = Enum.Font.GothamMedium
    KeyInput.TextSize = 15
    KeyInput.TextXAlignment = Enum.TextXAlignment.Left
    KeyInput.Parent = InputFrame
    
    local VerifyButton = Instance.new("TextButton")
    VerifyButton.Size = UDim2.new(1, 0, 0, 50)
    VerifyButton.Position = UDim2.new(0, 0, 0, 145)
    VerifyButton.BackgroundColor3 = COLORS.Primary
    VerifyButton.Text = "✓ VERIFICAR KEY"
    VerifyButton.TextColor3 = COLORS.Text
    VerifyButton.Font = Enum.Font.GothamBold
    VerifyButton.TextSize = 16
    VerifyButton.Parent = Content
    Instance.new("UICorner", VerifyButton).CornerRadius = UDim.new(0, 10)
    
    local GetKeyButton = Instance.new("TextButton")
    GetKeyButton.Size = UDim2.new(1, 0, 0, 50)
    GetKeyButton.Position = UDim2.new(0, 0, 0, 205)
    GetKeyButton.BackgroundColor3 = COLORS.KeyButton
    GetKeyButton.Text = "🔑 PEGAR KEY AQUI"
    GetKeyButton.TextColor3 = COLORS.Text
    GetKeyButton.Font = Enum.Font.GothamBold
    GetKeyButton.TextSize = 16
    GetKeyButton.Parent = Content
    Instance.new("UICorner", GetKeyButton).CornerRadius = UDim.new(0, 10)
    
    local DiscordButton = Instance.new("TextButton")
    DiscordButton.Size = UDim2.new(1, 0, 0, 50)
    DiscordButton.Position = UDim2.new(0, 0, 0, 265)
    DiscordButton.BackgroundColor3 = COLORS.Accent
    DiscordButton.Text = "💬 DISCORD CRIADOR"
    DiscordButton.TextColor3 = COLORS.Text
    DiscordButton.Font = Enum.Font.GothamBold
    DiscordButton.TextSize = 16
    DiscordButton.Parent = Content
    Instance.new("UICorner", DiscordButton).CornerRadius = UDim.new(0, 10)
    
    local StatusLabel = Instance.new("TextLabel")
    StatusLabel.Size = UDim2.new(1, 0, 0, 25)
    StatusLabel.Position = UDim2.new(0, 0, 1, -30)
    StatusLabel.BackgroundTransparency = 1
    StatusLabel.Text = ""
    StatusLabel.TextColor3 = COLORS.Text
    StatusLabel.Font = Enum.Font.GothamMedium
    StatusLabel.TextSize = 13
    StatusLabel.Visible = false
    StatusLabel.Parent = MainContainer
    
    return ScreenGui, {MainContainer = MainContainer, CloseButton = CloseButton, KeyInput = KeyInput, 
           VerifyButton = VerifyButton, GetKeyButton = GetKeyButton, DiscordButton = DiscordButton, 
           StatusLabel = StatusLabel}
end

local function IsTouchOnButton(touchPos)
    local screenSize = workspace.CurrentCamera.ViewportSize
    local touchX, touchY = touchPos.X, touchPos.Y
    return (touchX < screenSize.X * 0.25 and touchY > screenSize.Y * 0.6) or 
           (touchX > screenSize.X * 0.75 and touchY > screenSize.Y * 0.6)
end

local function StartKeySystem(onSuccess)
    local savedKey = LoadSavedKey()
    if savedKey and VerifyKey(savedKey) then
        print("✅ Key verificada automaticamente!")
        task.wait(0.5)
        if onSuccess then onSuccess() end
        return
    end
    
    local gui, elements = CreateKeySystem()
    gui.Parent = CoreGui
    gui.Enabled = false
    
    local activeTouches, keySystemOpen = {}, false
    
    UserInputService.TouchStarted:Connect(function(touch)
        if keySystemOpen then return end
        if not IsTouchOnButton(touch.Position) then activeTouches[touch] = true end
        
        local count = 0
        for _, active in pairs(activeTouches) do if active then count = count + 1 end end
        
        if count >= 3 then
            keySystemOpen = true
            gui.Enabled = true
            elements.MainContainer.Size = UDim2.new(0, 0, 0, 0)
            Tween(elements.MainContainer, {Size = UDim2.new(0, 500, 0, 420), Position = UDim2.new(0.5, -250, 0.5, -210)}, 0.5, Enum.EasingStyle.Back)
        end
    end)
    
    UserInputService.TouchEnded:Connect(function(touch) activeTouches[touch] = false end)
    
    local function ShowStatus(msg, success)
        elements.StatusLabel.Text = msg
        elements.StatusLabel.TextColor3 = success and COLORS.Success or COLORS.Error
        elements.StatusLabel.Visible = true
        task.wait(2)
        elements.StatusLabel.Visible = false
    end
    
    elements.VerifyButton.MouseButton1Click:Connect(function()
        local key = elements.KeyInput.Text:gsub("^%s*(.-)%s*$", "%1")
        if key == "" then ShowStatus("❌ Digite uma key!", false) return end
        
        if VerifyKey(key) then
            ShowStatus("✅ Key válida!", true)
            SaveKey(key)
            task.wait(1)
            gui:Destroy()
            if onSuccess then onSuccess() end
        else
            ShowStatus("❌ Key inválida!", false)
            elements.KeyInput.Text = ""
        end
    end)
    
    elements.GetKeyButton.MouseButton1Click:Connect(function()
        setclipboard(KEY_CONFIG.KeyLink)
        ShowStatus("🔑 Link copiado!", true)
    end)
    
    elements.DiscordButton.MouseButton1Click:Connect(function()
        setclipboard(KEY_CONFIG.DiscordLink)
        ShowStatus("💬 Discord copiado!", true)
    end)
    
    elements.CloseButton.MouseButton1Click:Connect(function() gui:Destroy() end)
end

StartKeySystem(function()
    print("✅ Carregando HUB...")
    
    local Camera = workspace.CurrentCamera
    local RunService = game:GetService("RunService")
    local Teams = game:GetService("Teams")

    local Settings = {
        Aimbot = {Enabled = false, FOV = 150, WallCheck = true, TargetPart = "Head", TeamCheck = true},
        ESP = {Enabled = false, BoxColor = Color3.fromRGB(255, 0, 255), NameColor = Color3.fromRGB(255, 255, 255), 
               DistanceColor = Color3.fromRGB(0, 255, 255), HealthBarEnabled = true},
        AutoTeleport = {Enabled = false, Delay = 2}  -- Delay padrão: 2 segundos (mais rápido)
    }

    local function HasMultipleTeams()
        local count = 0
        for _ in pairs(Teams:GetTeams()) do count = count + 1 end
        return count > 1
    end

    local function IsEnemy(player)
        if not Settings.Aimbot.TeamCheck or not HasMultipleTeams() then return true end
        if LocalPlayer.Team and player.Team then return LocalPlayer.Team ~= player.Team end
        return true
    end

    local function IsVisible(targetChar)
        if not Settings.Aimbot.WallCheck then return true end
        local char = LocalPlayer.Character
        if not char then return false end
        local origin = char:FindFirstChild("HumanoidRootPart")
        local target = targetChar:FindFirstChild(Settings.Aimbot.TargetPart)
        if not origin or not target then return false end
        local ray = Ray.new(origin.Position, (target.Position - origin.Position).Unit * 1000)
        local hit = workspace:FindPartOnRayWithIgnoreList(ray, {char, Camera})
        return hit and hit:IsDescendantOf(targetChar)
    end

    local function GetClosestPlayerInFOV()
        local closestPlayer, shortestDistance = nil, Settings.Aimbot.FOV
        local screenCenter = Camera.ViewportSize / 2 -- Centro da tela
        
        for _, player in pairs(Players:GetPlayers()) do
            if player ~= LocalPlayer and player.Character and IsEnemy(player) then
                local char = player.Character
                local humanoid = char:FindFirstChild("Humanoid")
                local targetPart = char:FindFirstChild(Settings.Aimbot.TargetPart)
                if humanoid and humanoid.Health > 0 and targetPart then
                    local screenPos, onScreen = Camera:WorldToViewportPoint(targetPart.Position)
                    if onScreen then
                        -- Calcula distância do centro da tela (onde está o FOV)
                        local distance = (Vector2.new(screenPos.X, screenPos.Y) - screenCenter).Magnitude
                        
                        -- Verifica se está dentro do FOV e é o mais próximo
                        if distance < shortestDistance and IsVisible(char) then
                            closestPlayer = player
                            shortestDistance = distance
                        end
                    end
                end
            end
        end
        return closestPlayer
    end

    -- AIMBOT MELHORADO
    local aimbotConnection
    aimbotConnection = RunService.RenderStepped:Connect(function()
        if Settings.Aimbot.Enabled then
            local target = GetClosestPlayerInFOV()
            if target and target.Character then
                local targetPart = target.Character:FindFirstChild(Settings.Aimbot.TargetPart)
                if targetPart then
                    -- Aimbot FORTE - mira diretamente
                    Camera.CFrame = CFrame.new(Camera.CFrame.Position, targetPart.Position)
                end
            end
        end
    end)

    local ESPObjects = {}

    local function CreateESP(player)
        if ESPObjects[player] then return end
        ESPObjects[player] = {
            Box = Drawing.new("Square"),
            Name = Drawing.new("Text"),
            Distance = Drawing.new("Text"),
            HealthBar = Drawing.new("Line"),
            HealthBarBG = Drawing.new("Line")
        }
        local esp = ESPObjects[player]
        esp.Box.Thickness = 2
        esp.Box.Filled = false
        esp.Box.Visible = false
        esp.Box.ZIndex = 2
        esp.Name.Size = 14
        esp.Name.Center = true
        esp.Name.Outline = true
        esp.Name.Visible = false
        esp.Name.ZIndex = 2
        esp.Distance.Size = 12
        esp.Distance.Center = true
        esp.Distance.Outline = true
        esp.Distance.Visible = false
        esp.Distance.ZIndex = 2
        esp.HealthBarBG.Thickness = 3
        esp.HealthBarBG.Color = Color3.fromRGB(0, 0, 0)
        esp.HealthBarBG.Visible = false
        esp.HealthBar.Thickness = 3
        esp.HealthBar.Visible = false
        esp.HealthBar.ZIndex = 2
    end

    spawn(function()
        while true do
            for _, player in pairs(Players:GetPlayers()) do
                if player ~= LocalPlayer and not ESPObjects[player] then CreateESP(player) end
            end
            task.wait(1)
        end
    end)

    local function UpdateESP()
        for player, esp in pairs(ESPObjects) do
            if player.Character and player.Character:FindFirstChild("HumanoidRootPart") and player.Character:FindFirstChild("Humanoid") then
                local char = player.Character
                local hrp = char.HumanoidRootPart
                local humanoid = char.Humanoid
                local screenPos, onScreen = Camera:WorldToViewportPoint(hrp.Position)
                
                if onScreen and Settings.ESP.Enabled then
                    local headPos = Camera:WorldToViewportPoint(char.Head.Position + Vector3.new(0, 0.5, 0))
                    local legPos = Camera:WorldToViewportPoint(hrp.Position - Vector3.new(0, 3, 0))
                    local height = math.abs(headPos.Y - legPos.Y)
                    local width = height / 2
                    
                    local boxColor = Settings.ESP.BoxColor
                    if HasMultipleTeams() and player.Team then
                        boxColor = player.Team == LocalPlayer.Team and Color3.fromRGB(0, 255, 0) or Color3.fromRGB(255, 0, 0)
                    end
                    
                    esp.Box.Size = Vector2.new(width, height)
                    esp.Box.Position = Vector2.new(screenPos.X - width / 2, screenPos.Y - height / 2)
                    esp.Box.Color = boxColor
                    esp.Box.Visible = true
                    
                    esp.Name.Text = player.Name
                    esp.Name.Position = Vector2.new(screenPos.X, headPos.Y - 20)
                    esp.Name.Color = Settings.ESP.NameColor
                    esp.Name.Visible = true
                    
                    local distance = math.floor((hrp.Position - LocalPlayer.Character.HumanoidRootPart.Position).Magnitude)
                    esp.Distance.Text = tostring(distance) .. "m"
                    esp.Distance.Position = Vector2.new(screenPos.X, legPos.Y + 5)
                    esp.Distance.Color = Settings.ESP.DistanceColor
                    esp.Distance.Visible = true
                    
                    if Settings.ESP.HealthBarEnabled then
                        local healthPercent = humanoid.Health / humanoid.MaxHealth
                        esp.HealthBarBG.From = Vector2.new(screenPos.X - width / 2 - 6, screenPos.Y - height / 2)
                        esp.HealthBarBG.To = Vector2.new(screenPos.X - width / 2 - 6, screenPos.Y + height / 2)
                        esp.HealthBarBG.Visible = true
                        esp.HealthBar.From = Vector2.new(screenPos.X - width / 2 - 6, screenPos.Y - height / 2)
                        esp.HealthBar.To = Vector2.new(screenPos.X - width / 2 - 6, screenPos.Y - height / 2 + height * healthPercent)
                        esp.HealthBar.Color = Color3.fromRGB(255 * (1 - healthPercent), 255 * healthPercent, 0)
                        esp.HealthBar.Visible = true
                    end
                else
                    esp.Box.Visible = false
                    esp.Name.Visible = false
                    esp.Distance.Visible = false
                    esp.HealthBar.Visible = false
                    esp.HealthBarBG.Visible = false
                end
            else
                esp.Box.Visible = false
                esp.Name.Visible = false
                esp.Distance.Visible = false
                esp.HealthBar.Visible = false
                esp.HealthBarBG.Visible = false
            end
        end
    end

    Players.PlayerRemoving:Connect(function(player)
        if ESPObjects[player] then
            for _, drawing in pairs(ESPObjects[player]) do drawing:Remove() end
            ESPObjects[player] = nil
        end
    end)

    RunService.RenderStepped:Connect(UpdateESP)

    -- AUTO TELEPORT ULTRA RÁPIDO
    spawn(function()
        while true do
            if Settings.AutoTeleport.Enabled and LocalPlayer.Character and LocalPlayer.Character:FindFirstChild("HumanoidRootPart") then
                local myHRP = LocalPlayer.Character.HumanoidRootPart
                
                -- Pega todos os players válidos
                for _, player in pairs(Players:GetPlayers()) do
                    if player ~= LocalPlayer and player.Character and player.Character:FindFirstChild("HumanoidRootPart") then
                        local targetHRP = player.Character.HumanoidRootPart
                        
                        -- Teleporte INSTANTÂNEO sem delay
                        myHRP.CFrame = targetHRP.CFrame * CFrame.new(0, 2, 0) -- Ligeiramente acima
                        
                        -- Delay configurável entre players
                        task.wait(Settings.AutoTeleport.Delay)
                        break
                    end
                end
            end
            task.wait(0.1) -- Loop muito mais rápido
        end
    end)

    -- FOV CIRCLE COM GUI (FUNCIONA EM MOBILE!)
    local FOVCircleGui = Instance.new("ScreenGui")
    FOVCircleGui.Name = "KakaFOVCircle"
    FOVCircleGui.ResetOnSpawn = false
    FOVCircleGui.IgnoreGuiInset = true
    FOVCircleGui.Parent = CoreGui
    
    local FOVCircle = Instance.new("Frame")
    FOVCircle.Name = "FOVCircle"
    FOVCircle.AnchorPoint = Vector2.new(0.5, 0.5)
    FOVCircle.Position = UDim2.new(0.5, 0, 0.5, 0)
    FOVCircle.Size = UDim2.new(0, Settings.Aimbot.FOV * 2, 0, Settings.Aimbot.FOV * 2)
    FOVCircle.BackgroundTransparency = 1
    FOVCircle.Parent = FOVCircleGui
    
    local FOVCorner = Instance.new("UICorner")
    FOVCorner.CornerRadius = UDim.new(1, 0)
    FOVCorner.Parent = FOVCircle
    
    local FOVStroke = Instance.new("UIStroke")
    FOVStroke.Thickness = 3
    FOVStroke.Transparency = 0
    FOVStroke.Parent = FOVCircle
    
    -- Rainbow effect
    local hue = 0
    spawn(function()
        while true do
            if FOVCircleGui and FOVCircleGui.Parent then
                hue = (hue + 1) % 360
                FOVStroke.Color = Color3.fromHSV(hue / 360, 1, 1)
                
                -- Atualiza tamanho do FOV
                FOVCircle.Size = UDim2.new(0, Settings.Aimbot.FOV * 2, 0, Settings.Aimbot.FOV * 2)
                
                task.wait(0.03) -- ~30 FPS para rainbow
            else
                break
            end
        end
    end)

    local ScreenGui = Instance.new("ScreenGui")
    ScreenGui.Name = "KakaHubV4"
    ScreenGui.ResetOnSpawn = false
    ScreenGui.Parent = LocalPlayer.PlayerGui

    local MainFrame = Instance.new("Frame")
    MainFrame.Size = UDim2.new(0, 450, 0, 650) -- Aumentado para caber mensagem
    MainFrame.Position = UDim2.new(0.5, -225, 0.5, -325)
    MainFrame.BackgroundColor3 = Color3.fromRGB(25, 25, 35)
    MainFrame.BorderSizePixel = 0
    MainFrame.Active = true
    MainFrame.Draggable = true
    MainFrame.Visible = false
    MainFrame.Parent = ScreenGui
    Instance.new("UICorner", MainFrame).CornerRadius = UDim.new(0, 15)
    
    -- CORAÇÕES ANIMADOS NO FUNDO
    local function CreateHeart(parent, size, position)
        local heart = Instance.new("TextLabel")
        heart.Size = UDim2.new(0, size, 0, size)
        heart.Position = position
        heart.BackgroundTransparency = 1
        heart.Text = "❤️"
        heart.TextSize = size
        heart.TextTransparency = 0.7
        heart.ZIndex = 0
        heart.Parent = parent
        
        -- Animação de pulsar
        spawn(function()
            while heart and heart.Parent do
                heart.TextTransparency = 0.7
                task.wait(0.5)
                heart.TextTransparency = 0.9
                task.wait(0.5)
            end
        end)
        
        return heart
    end
    
    -- Criar vários corações no fundo
    CreateHeart(MainFrame, 40, UDim2.new(0, 20, 0, 100))
    CreateHeart(MainFrame, 35, UDim2.new(1, -60, 0, 150))
    CreateHeart(MainFrame, 30, UDim2.new(0, 30, 0, 400))
    CreateHeart(MainFrame, 45, UDim2.new(1, -70, 0, 450))
    CreateHeart(MainFrame, 25, UDim2.new(0.5, -15, 0, 250))

    local Header = Instance.new("Frame")
    Header.Size = UDim2.new(1, 0, 0, 60)
    Header.BackgroundColor3 = Color3.fromRGB(255, 105, 180) -- Rosa pink romântico
    Header.BorderSizePixel = 0
    Header.Parent = MainFrame
    Instance.new("UICorner", Header).CornerRadius = UDim.new(0, 15)

    local HeaderFix = Instance.new("Frame")
    HeaderFix.Size = UDim2.new(1, 0, 0, 15)
    HeaderFix.Position = UDim2.new(0, 0, 1, -15)
    HeaderFix.BackgroundColor3 = Color3.fromRGB(255, 105, 180)
    HeaderFix.BorderSizePixel = 0
    HeaderFix.Parent = Header

    local Title = Instance.new("TextLabel")
    Title.Size = UDim2.new(1, -20, 1, 0)
    Title.Position = UDim2.new(0, 10, 0, 0)
    Title.BackgroundTransparency = 1
    Title.Text = "💕 KAKA HUB V4 (VALENTINES)"
    Title.TextColor3 = Color3.fromRGB(255, 255, 255)
    Title.TextSize = 24
    Title.Font = Enum.Font.GothamBold
    Title.TextXAlignment = Enum.TextXAlignment.Left
    Title.Parent = Header

    local CloseButton = Instance.new("TextButton")
    CloseButton.Size = UDim2.new(0, 40, 0, 40)
    CloseButton.Position = UDim2.new(1, -50, 0, 10)
    CloseButton.BackgroundColor3 = Color3.fromRGB(255, 50, 50)
    CloseButton.Text = "X"
    CloseButton.TextColor3 = Color3.fromRGB(255, 255, 255)
    CloseButton.TextSize = 20
    CloseButton.Font = Enum.Font.GothamBold
    CloseButton.Parent = Header
    Instance.new("UICorner", CloseButton).CornerRadius = UDim.new(0, 10)

    local ContentFrame = Instance.new("ScrollingFrame")
    ContentFrame.Size = UDim2.new(1, -20, 1, -170) -- Reduzido para dar espaço à mensagem
    ContentFrame.Position = UDim2.new(0, 10, 0, 70)
    ContentFrame.BackgroundTransparency = 1
    ContentFrame.BorderSizePixel = 0
    ContentFrame.ScrollBarThickness = 6
    ContentFrame.Parent = MainFrame

    local UIListLayout = Instance.new("UIListLayout")
    UIListLayout.Padding = UDim.new(0, 10)
    UIListLayout.Parent = ContentFrame

    local function CreateSection(title)
        local section = Instance.new("Frame")
        section.Size = UDim2.new(1, -10, 0, 40)
        section.BackgroundColor3 = Color3.fromRGB(35, 35, 50)
        section.BorderSizePixel = 0
        section.Parent = ContentFrame
        Instance.new("UICorner", section).CornerRadius = UDim.new(0, 8)
        
        local label = Instance.new("TextLabel")
        label.Size = UDim2.new(1, -10, 1, 0)
        label.Position = UDim2.new(0, 10, 0, 0)
        label.BackgroundTransparency = 1
        label.Text = title
        label.TextColor3 = Color3.fromRGB(255, 200, 0)
        label.TextSize = 16
        label.Font = Enum.Font.GothamBold
        label.TextXAlignment = Enum.TextXAlignment.Left
        label.Parent = section
    end

    local function CreateToggle(name, default, callback)
        local toggle = Instance.new("Frame")
        toggle.Size = UDim2.new(1, -10, 0, 40)
        toggle.BackgroundColor3 = Color3.fromRGB(35, 35, 50)
        toggle.BorderSizePixel = 0
        toggle.Parent = ContentFrame
        Instance.new("UICorner", toggle).CornerRadius = UDim.new(0, 8)
        
        local label = Instance.new("TextLabel")
        label.Size = UDim2.new(0.7, 0, 1, 0)
        label.Position = UDim2.new(0, 10, 0, 0)
        label.BackgroundTransparency = 1
        label.Text = name
        label.TextColor3 = Color3.fromRGB(255, 255, 255)
        label.TextSize = 14
        label.Font = Enum.Font.Gotham
        label.TextXAlignment = Enum.TextXAlignment.Left
        label.Parent = toggle
        
        local button = Instance.new("TextButton")
        button.Size = UDim2.new(0, 60, 0, 30)
        button.Position = UDim2.new(1, -70, 0.5, -15)
        button.BackgroundColor3 = default and Color3.fromRGB(0, 200, 0) or Color3.fromRGB(200, 0, 0)
        button.Text = default and "ON" or "OFF"
        button.TextColor3 = Color3.fromRGB(255, 255, 255)
        button.TextSize = 14
        button.Font = Enum.Font.GothamBold
        button.Parent = toggle
        Instance.new("UICorner", button).CornerRadius = UDim.new(0, 8)
        
        local enabled = default
        button.MouseButton1Click:Connect(function()
            enabled = not enabled
            button.BackgroundColor3 = enabled and Color3.fromRGB(0, 200, 0) or Color3.fromRGB(200, 0, 0)
            button.Text = enabled and "ON" or "OFF"
            callback(enabled)
        end)
    end

    local function CreateSlider(name, min, max, default, callback)
        local slider = Instance.new("Frame")
        slider.Size = UDim2.new(1, -10, 0, 60)
        slider.BackgroundColor3 = Color3.fromRGB(35, 35, 50)
        slider.BorderSizePixel = 0
        slider.Parent = ContentFrame
        Instance.new("UICorner", slider).CornerRadius = UDim.new(0, 8)
        
        local label = Instance.new("TextLabel")
        label.Size = UDim2.new(1, -20, 0, 20)
        label.Position = UDim2.new(0, 10, 0, 5)
        label.BackgroundTransparency = 1
        label.Text = name .. ": " .. default
        label.TextColor3 = Color3.fromRGB(255, 255, 255)
        label.TextSize = 14
        label.Font = Enum.Font.Gotham
        label.TextXAlignment = Enum.TextXAlignment.Left
        label.Parent = slider
        
        local sliderBar = Instance.new("Frame")
        sliderBar.Size = UDim2.new(0.9, 0, 0, 8)
        sliderBar.Position = UDim2.new(0.05, 0, 0, 35)
        sliderBar.BackgroundColor3 = Color3.fromRGB(50, 50, 70)
        sliderBar.BorderSizePixel = 0
        sliderBar.Parent = slider
        Instance.new("UICorner", sliderBar).CornerRadius = UDim.new(1, 0)
        
        local sliderFill = Instance.new("Frame")
        sliderFill.Size = UDim2.new((default - min) / (max - min), 0, 1, 0)
        sliderFill.BackgroundColor3 = Color3.fromRGB(255, 0, 150)
        sliderFill.BorderSizePixel = 0
        sliderFill.Parent = sliderBar
        Instance.new("UICorner", sliderFill).CornerRadius = UDim.new(1, 0)
        
        local sliderButton = Instance.new("TextButton")
        sliderButton.Size = UDim2.new(1, 0, 1, 0)
        sliderButton.BackgroundTransparency = 1
        sliderButton.Text = ""
        sliderButton.Parent = sliderBar
        
        local dragging = false
        sliderButton.MouseButton1Down:Connect(function() dragging = true end)
        UserInputService.InputEnded:Connect(function(input)
            if input.UserInputType == Enum.UserInputType.MouseButton1 then dragging = false end
        end)
        
        sliderButton.MouseMoved:Connect(function()
            if dragging then
                local mousePos = UserInputService:GetMouseLocation().X
                local value = math.clamp((mousePos - sliderBar.AbsolutePosition.X) / sliderBar.AbsoluteSize.X, 0, 1)
                local actualValue = math.floor(min + (max - min) * value)
                sliderFill.Size = UDim2.new(value, 0, 1, 0)
                label.Text = name .. ": " .. actualValue
                callback(actualValue)
            end
        end)
    end

    CreateSection("🎯 AIMBOT")
    CreateToggle("Aimbot", false, function(enabled) Settings.Aimbot.Enabled = enabled end)
    CreateToggle("Team Check", true, function(enabled) Settings.Aimbot.TeamCheck = enabled end)
    CreateSlider("FOV Circle", 50, 500, 150, function(value) Settings.Aimbot.FOV = value end)
    
    CreateSection("👁️ ESP (Loop Automático)")
    CreateToggle("ESP", false, function(enabled) Settings.ESP.Enabled = enabled end)
    
    CreateSection("🚁 AUTO TELEPORT")
    CreateToggle("Auto TP Players", false, function(enabled) Settings.AutoTeleport.Enabled = enabled end)
    CreateSlider("Delay (segundos)", 0.5, 10, 2, function(value) Settings.AutoTeleport.Delay = value end)

    -- ═══════════════════════════════════════════════════════════
    --  💝 MENSAGEM ROMÂNTICA (DENTRO DO SCROLL)
    -- ═══════════════════════════════════════════════════════════
    
    local RomanticMessage = Instance.new("Frame")
    RomanticMessage.Name = "RomanticMessage"
    RomanticMessage.Size = UDim2.new(1, -10, 0, 90)
    RomanticMessage.BackgroundColor3 = Color3.fromRGB(255, 105, 180)
    RomanticMessage.BorderSizePixel = 0
    RomanticMessage.Parent = ContentFrame -- DENTRO DO SCROLL!
    
    local MessageCorner = Instance.new("UICorner")
    MessageCorner.CornerRadius = UDim.new(0, 12)
    MessageCorner.Parent = RomanticMessage
    
    local MessageStroke = Instance.new("UIStroke")
    MessageStroke.Color = Color3.fromRGB(255, 255, 255)
    MessageStroke.Thickness = 3
    MessageStroke.Parent = RomanticMessage
    
    local CreditText = Instance.new("TextLabel")
    CreditText.Size = UDim2.new(1, -20, 0, 40)
    CreditText.Position = UDim2.new(0, 10, 0, 5)
    CreditText.BackgroundTransparency = 1
    CreditText.Text = "💻 Script feito por Carlos"
    CreditText.TextColor3 = Color3.fromRGB(255, 255, 255)
    CreditText.TextSize = 18
    CreditText.Font = Enum.Font.GothamBold
    CreditText.TextXAlignment = Enum.TextXAlignment.Center
    CreditText.Parent = RomanticMessage
    
    local LoveText = Instance.new("TextLabel")
    LoveText.Size = UDim2.new(1, -20, 0, 40)
    LoveText.Position = UDim2.new(0, 10, 0, 45)
    LoveText.BackgroundTransparency = 1
    LoveText.Text = "💕 Te amo Sara 💕"
    LoveText.TextColor3 = Color3.fromRGB(255, 255, 255)
    LoveText.TextSize = 20
    LoveText.Font = Enum.Font.GothamBold
    LoveText.TextXAlignment = Enum.TextXAlignment.Center
    LoveText.Parent = RomanticMessage
    
    -- Animação de pulsar
    spawn(function()
        local toggle = true
        while RomanticMessage and RomanticMessage.Parent do
            if toggle then
                RomanticMessage.BackgroundColor3 = Color3.fromRGB(255, 182, 193)
            else
                RomanticMessage.BackgroundColor3 = Color3.fromRGB(255, 105, 180)
            end
            toggle = not toggle
            task.wait(1)
        end
    end)
    
    print("💝 Mensagem romântica criada no ContentFrame!")

    CloseButton.MouseButton1Click:Connect(function() MainFrame.Visible = false end)

    local hubTouches, hubDebounce = {}, false
    local destroyTouches = {}

    UserInputService.TouchStarted:Connect(function(touch)
        if not IsTouchOnButton(touch.Position) then 
            hubTouches[touch] = true 
            destroyTouches[touch] = true
        end
        
        -- Conta toques para abrir/fechar hub (3 dedos)
        local hubCount = 0
        for _, active in pairs(hubTouches) do if active then hubCount = hubCount + 1 end end
        
        -- Conta toques para destruir (6 dedos)
        local destroyCount = 0
        for _, active in pairs(destroyTouches) do if active then destroyCount = destroyCount + 1 end end
        
        -- DESTRUIR COM 6 DEDOS
        if destroyCount >= 6 then
            print("🗑️ Destruindo KAKA HUB V4...")
            
            -- Destroi GUI do Hub
            if ScreenGui then
                ScreenGui:Destroy()
            end
            
            -- Destroi FOV Circle
            if FOVCircleGui then
                FOVCircleGui:Destroy()
            end
            
            -- Desativa Aimbot
            Settings.Aimbot.Enabled = false
            if aimbotConnection then
                aimbotConnection:Disconnect()
            end
            
            -- Desativa ESP
            Settings.ESP.Enabled = false
            for player, esp in pairs(ESPObjects) do
                for _, drawing in pairs(esp) do
                    drawing:Remove()
                end
            end
            ESPObjects = {}
            
            -- Desativa Auto Teleport
            Settings.AutoTeleport.Enabled = false
            
            print("✅ Hub destruído com sucesso!")
            return
        end
        
        -- Abrir/Fechar Hub com 3 dedos
        if hubCount >= 3 and hubCount < 6 and not hubDebounce then
            hubDebounce = true
            MainFrame.Visible = not MainFrame.Visible
            task.wait(1)
            hubDebounce = false
        end
    end)

    UserInputService.TouchEnded:Connect(function(touch) 
        hubTouches[touch] = false 
        destroyTouches[touch] = false
    end)

    print("✅ KAKA HUB V4 carregado!")
end)
