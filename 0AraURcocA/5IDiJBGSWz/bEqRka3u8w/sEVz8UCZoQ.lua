local obf_stringchar = string.char;
local obf_stringbyte = string.byte;
local obf_stringsub = string.sub;
local obf_bitlib = bit32 or bit;
local obf_XOR = obf_bitlib.bxor;
local obf_tableconcat = table.concat;
local obf_tableinsert = table.insert;
local function LUAOBFUSACTOR_DECRYPT_STR_0(LUAOBFUSACTOR_STR, LUAOBFUSACTOR_KEY)
	local result = {};
	for i = 1, #LUAOBFUSACTOR_STR do
		obf_tableinsert(result, obf_stringchar(obf_XOR(obf_stringbyte(obf_stringsub(LUAOBFUSACTOR_STR, i, i + 1)), obf_stringbyte(obf_stringsub(LUAOBFUSACTOR_KEY, 1 + (i % #LUAOBFUSACTOR_KEY), 1 + (i % #LUAOBFUSACTOR_KEY) + 1))) % 256));
	end
	return obf_tableconcat(result);
end
local v0 = {};
local v1 = game:GetService(LUAOBFUSACTOR_DECRYPT_STR_0("\65\39\6\15\253\99\56", "\152\17\75\103\118"));
local v2 = game:GetService(LUAOBFUSACTOR_DECRYPT_STR_0("\44\194\68\124\29\186\217\0\27\195\103\100\27\171\217\19\27", "\116\126\167\52\16\116\217\184"));
local v3 = game:GetService(LUAOBFUSACTOR_DECRYPT_STR_0("\25\47\146\191\10\82\201\45\37", "\168\78\64\224\212\121\34"));
local v4 = v1.LocalPlayer;
local v5;
local v6 = 19 + 1;
local v7 = 473 - (10 + 438);
local v8 = false;
local v9 = false;
local v10 = true;
local v11 = false;
local v12 = false;
local v13;
local v14;
local v15 = false;
local v16 = v2:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\220\160\240\247\66\45\71\203\179\248\246\66\59", "\103\142\197\157\152\54\72")) and v2[LUAOBFUSACTOR_DECRYPT_STR_0("\23\91\72\83\44\32\30\96\74\61\43\74\86", "\88\69\62\37\60")]:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\222\210\28\91\86", "\164\142\167\114\56\62\101"));
local function v17(v34)
	local v35 = 0 + 0;
	local v36;
	while true do
		if (v35 == (3 - 2)) then
			return v36;
		end
		if (v35 == (0 + 0)) then
			v36 = {};
			for v91, v92 in ipairs({LUAOBFUSACTOR_DECRYPT_STR_0("\197\64\197\188", "\71\141\37\164\216"),LUAOBFUSACTOR_DECRYPT_STR_0("\201\4\192\245\62", "\187\157\107\178\134\81"),LUAOBFUSACTOR_DECRYPT_STR_0("\210\41\172\44\78\163\212\171", "\198\158\76\202\88\110\226\166"),LUAOBFUSACTOR_DECRYPT_STR_0("\241\6\133\255\222\131\46\144\250", "\170\163\111\226\151"),LUAOBFUSACTOR_DECRYPT_STR_0("\61\53\180\44\14\27\44\22", "\73\113\80\210\88\46\87"),LUAOBFUSACTOR_DECRYPT_STR_0("\179\37\202\26\243\193\0\200\21", "\135\225\76\173\114")}) do
				local v93 = 0 - 0;
				local v94;
				while true do
					if (v93 == (0 + 0)) then
						v94 = v34:FindFirstChild(v92);
						if v94 then
							table.insert(v36, v94);
						end
						break;
					end
				end
			end
			v35 = 1 - 0;
		end
	end
end
local function v18(v37)
	local v38 = 0 + 0;
	local v39;
	while true do
		if (v38 == (1475 - (1329 + 145))) then
			return nil;
		end
		if (v38 == (971 - (140 + 831))) then
			v39 = v17(v37);
			if (#v39 > (1850 - (1409 + 441))) then
				return v39[math.random(719 - (15 + 703), #v39)];
			end
			v38 = 1 + 0;
		end
	end
end
local function v19(v40, v41, v42, v43)
	local v44 = 438 - (262 + 176);
	local v45;
	local v46;
	while true do
		if ((1721 - (345 + 1376)) == v44) then
			v45 = (v42 - v40).Unit;
			v46 = v41:Dot(v45);
			v44 = 689 - (198 + 490);
		end
		if (v44 == (4 - 3)) then
			if (v46 <= (0.3 - 0)) then
				return false;
			end
			if v12 then
				local v95 = 1206 - (696 + 510);
				local v96;
				local v97;
				while true do
					if ((1 - 0) == v95) then
						v96.FilterDescendantsInstances = {v5};
						v97 = v3:Raycast(v40, v45 * v6, v96);
						v95 = 1 + 1;
					end
					if (v95 == (6 - 4)) then
						if (v97 and not v97.Instance:IsDescendantOf(v43)) then
							return false;
						end
						break;
					end
					if (v95 == (0 - 0)) then
						v96 = RaycastParams.new();
						v96.FilterType = Enum.RaycastFilterType.Blacklist;
						v95 = 375 - (123 + 251);
					end
				end
			end
			v44 = 9 - 7;
		end
		if ((700 - (208 + 490)) == v44) then
			return true;
		end
	end
end
local function v20()
	local v47;
	local v48 = math.huge;
	local v49 = v5 and v5:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\50\248\181\177\162\178\174\30\223\183\191\184\141\166\8\249", "\199\122\141\216\208\204\221"));
	if not v49 then
		return nil;
	end
	for v71, v72 in ipairs(v3:GetDescendants()) do
		if (v72:IsA(LUAOBFUSACTOR_DECRYPT_STR_0("\128\210\20\245\116", "\150\205\189\112\144\24")) and (v72 ~= v5)) then
			local v74 = 0 + 0;
			local v75;
			while true do
				if ((0 + 0) == v74) then
					v75 = v72:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\13\145\178\77\10\135\24\20\23\139\176\88\52\137\3\4", "\112\69\228\223\44\100\232\113"));
					if (v75 and (v10 or v1:GetPlayerFromCharacter(v72))) then
						local v104 = 836 - (660 + 176);
						local v105;
						while true do
							if ((0 + 0) == v104) then
								v105 = (v75.Position - v49.Position).Magnitude;
								if ((v105 <= v7) and (v105 < v48) and (not v9 or v19(v49.Position, v49.CFrame.LookVector, v75.Position, v72))) then
									local v109 = 202 - (14 + 188);
									while true do
										if (v109 == (675 - (534 + 141))) then
											v47 = v72;
											v48 = v105;
											break;
										end
									end
								end
								break;
							end
						end
					end
					break;
				end
			end
		end
	end
	return v47;
end
local function v21(v50)
	local v51 = 0 + 0;
	local v52;
	local v53;
	local v54;
	local v55;
	local v56;
	while true do
		if (v51 == (3 + 0)) then
			v55.FilterType = Enum.RaycastFilterType.Blacklist;
			v55.FilterDescendantsInstances = {v5};
			v51 = 8 - 4;
		end
		if (v51 == (2 - 0)) then
			v54 = (v53.Position - v52.Position).Unit;
			v55 = RaycastParams.new();
			v51 = 8 - 5;
		end
		if (v51 == (3 + 1)) then
			v56 = v3:Raycast(v52.Position, v54 * (v53.Position - v52.Position).Magnitude, v55);
			return (v56 and v56.Position) or v53.Position;
		end
		if (v51 == (1 + 0)) then
			v53 = v18(v50);
			if not v53 then
				return v50:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\252\10\10\210\184\115\143\208\45\8\220\162\76\135\198\11", "\230\180\127\103\179\214\28")).Position;
			end
			v51 = 398 - (115 + 281);
		end
		if (v51 == (0 - 0)) then
			v52 = v5 and v5:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\190\12\88\78\240\105\225\130\1", "\128\236\101\63\38\132\33"));
			if not v52 then
				return v50:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\132\188\28\69\184\228\198\168\155\30\75\162\219\206\190\189", "\175\204\201\113\36\214\139")).Position;
			end
			v51 = 1 + 0;
		end
	end
end
local function v22(v57)
	local v58 = 0 - 0;
	local v59;
	while true do
		if (v58 == (3 - 2)) then
			v14 = Instance.new(LUAOBFUSACTOR_DECRYPT_STR_0("\119\205\39\200", "\100\39\172\85\188"));
			v14.Name = LUAOBFUSACTOR_DECRYPT_STR_0("\155\113\170\149\50\161\113\163\133\33", "\83\205\24\217\224");
			v14.Size = Vector3.new(871 - (550 + 317), 8 - 2, 4 - 0);
			v58 = 5 - 3;
		end
		if (v58 == (287 - (134 + 151))) then
			v14.Transparency = 1665.5 - (970 + 695);
			v14.Anchored = true;
			v14.CanCollide = false;
			v58 = 5 - 2;
		end
		if (v58 == (1990 - (582 + 1408))) then
			v59 = v57:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\206\208\192\60\232\202\196\57\212\202\194\41\214\196\223\41", "\93\134\165\173"));
			if not v59 then
				return;
			end
			if v14 then
				v14:Destroy();
			end
			v58 = 3 - 2;
		end
		if (v58 == (3 - 0)) then
			v14.Color = Color3.new(3 - 2, 1824 - (1195 + 629), 0 - 0);
			v14.Material = Enum.Material.ForceField;
			v14.CFrame = v59.CFrame;
			v58 = 245 - (187 + 54);
		end
		if (v58 == (784 - (162 + 618))) then
			v14.Parent = v3;
			game:GetService(LUAOBFUSACTOR_DECRYPT_STR_0("\154\247\195\208\51\221", "\30\222\146\161\162\90\174\210")):AddItem(v14, 1 + 0);
			break;
		end
	end
end
local function v23()
	local v60 = 0 + 0;
	local v61;
	while true do
		if (v60 == (1 - 0)) then
			if v61 then
				local v98 = 0 - 0;
				local v99;
				while true do
					if (v98 == (0 + 0)) then
						v99 = v61:FindFirstChild(LUAOBFUSACTOR_DECRYPT_STR_0("\205\91\125\11\235\65\121\14\215\65\127\30\213\79\98\30", "\106\133\46\16"));
						if v99 then
							local v106 = 1636 - (1373 + 263);
							local v107;
							while true do
								if (v106 == (1000 - (451 + 549))) then
									v107 = (v11 and v21(v61)) or v99.Position;
									v16:FireServer(v61, v107);
									v106 = 1 + 0;
								end
								if (v106 == (1 - 0)) then
									if v8 then
										v22(v61);
									end
									break;
								end
							end
						end
						break;
					end
				end
			end
			break;
		end
		if (v60 == (0 - 0)) then
			if (not v15 or not v16) then
				return;
			end
			v61 = v20();
			v60 = 1385 - (746 + 638);
		end
	end
end
local function v24(v62)
	v5 = v62;
end
v0.start = function()
	local v63 = 0 + 0;
	while true do
		if (v63 == (0 - 0)) then
			if v13 then
				return;
			end
			v4.CharacterAdded:Connect(v24);
			v63 = 342 - (218 + 123);
		end
		if ((1582 - (1535 + 46)) == v63) then
			v5 = v4.Character or v4.CharacterAdded:Wait();
			v13 = v4:GetMouse().Button1Down:Connect(v23);
			v63 = 2 + 0;
		end
		if (v63 == (1 + 1)) then
			v15 = true;
			break;
		end
	end
end;
v0.stop = function()
	local v64 = 560 - (306 + 254);
	while true do
		if ((1 + 0) == v64) then
			v15 = false;
			break;
		end
		if (v64 == (0 - 0)) then
			if v13 then
				local v100 = 1467 - (899 + 568);
				while true do
					if (v100 == (0 + 0)) then
						v13:Disconnect();
						v13 = nil;
						break;
					end
				end
			end
			if v14 then
				v14:Destroy();
			end
			v64 = 2 - 1;
		end
	end
end;
v0.updateRange = function(v65)
	v6 = tonumber(v65) or (623 - (268 + 335));
end;
v0.toggleVisualizer = function(v66)
	v8 = v66;
end;
v0.toggleAngleCheck = function(v67)
	v9 = v67;
end;
v0.toggleIncludeNPCs = function(v68)
	v10 = v68;
end;
v0.toggleParticle = function(v69)
	v11 = v69;
end;
v0.toggleWallCheck = function(v70)
	v12 = v70;
end;
v0.getRange = function()
	return v6;
end;
return v0;
