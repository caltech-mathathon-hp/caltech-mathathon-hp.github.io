import ProteinFolding.Tetrahedral.BulkNearVertexValues

/-! Opaque finite vertex elimination with an arbitrary predicate.
No graph predicate is unfolded during this finite case analysis. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem bulkNearAllIndices_cases (P : Fin 234 → Prop)
    (h0 : P (0 : Fin 234))
    (h1 : P (1 : Fin 234))
    (h2 : P (2 : Fin 234))
    (h3 : P (3 : Fin 234))
    (h4 : P (4 : Fin 234))
    (h5 : P (5 : Fin 234))
    (h6 : P (6 : Fin 234))
    (h7 : P (7 : Fin 234))
    (h8 : P (8 : Fin 234))
    (h9 : P (9 : Fin 234))
    (h10 : P (10 : Fin 234))
    (h11 : P (11 : Fin 234))
    (h12 : P (12 : Fin 234))
    (h13 : P (13 : Fin 234))
    (h14 : P (14 : Fin 234))
    (h15 : P (15 : Fin 234))
    (h16 : P (16 : Fin 234))
    (h17 : P (17 : Fin 234))
    (h18 : P (18 : Fin 234))
    (h19 : P (19 : Fin 234))
    (h20 : P (20 : Fin 234))
    (h21 : P (21 : Fin 234))
    (h22 : P (22 : Fin 234))
    (h23 : P (23 : Fin 234))
    (h24 : P (24 : Fin 234))
    (h25 : P (25 : Fin 234))
    (h26 : P (26 : Fin 234))
    (h27 : P (27 : Fin 234))
    (h28 : P (28 : Fin 234))
    (h29 : P (29 : Fin 234))
    (h30 : P (30 : Fin 234))
    (h31 : P (31 : Fin 234))
    (h32 : P (32 : Fin 234))
    (h33 : P (33 : Fin 234))
    (h34 : P (34 : Fin 234))
    (h35 : P (35 : Fin 234))
    (h36 : P (36 : Fin 234))
    (h37 : P (37 : Fin 234))
    (h38 : P (38 : Fin 234))
    (h39 : P (39 : Fin 234))
    (h40 : P (40 : Fin 234))
    (h41 : P (41 : Fin 234))
    (h42 : P (42 : Fin 234))
    (h43 : P (43 : Fin 234))
    (h44 : P (44 : Fin 234))
    (h45 : P (45 : Fin 234))
    (h46 : P (46 : Fin 234))
    (h47 : P (47 : Fin 234))
    (h48 : P (48 : Fin 234))
    (h49 : P (49 : Fin 234))
    (h50 : P (50 : Fin 234))
    (h51 : P (51 : Fin 234))
    (h52 : P (52 : Fin 234))
    (h53 : P (53 : Fin 234))
    (h54 : P (54 : Fin 234))
    (h55 : P (55 : Fin 234))
    (h56 : P (56 : Fin 234))
    (h57 : P (57 : Fin 234))
    (h58 : P (58 : Fin 234))
    (h59 : P (59 : Fin 234))
    (h60 : P (60 : Fin 234))
    (h61 : P (61 : Fin 234))
    (h62 : P (62 : Fin 234))
    (h63 : P (63 : Fin 234))
    (h64 : P (64 : Fin 234))
    (h65 : P (65 : Fin 234))
    (h66 : P (66 : Fin 234))
    (h67 : P (67 : Fin 234))
    (h68 : P (68 : Fin 234))
    (h69 : P (69 : Fin 234))
    (h70 : P (70 : Fin 234))
    (h71 : P (71 : Fin 234))
    (h72 : P (72 : Fin 234))
    (h73 : P (73 : Fin 234))
    (h74 : P (74 : Fin 234))
    (h75 : P (75 : Fin 234))
    (h76 : P (76 : Fin 234))
    (h77 : P (77 : Fin 234))
    (h78 : P (78 : Fin 234))
    (h79 : P (79 : Fin 234))
    (h80 : P (80 : Fin 234))
    (h81 : P (81 : Fin 234))
    (h82 : P (82 : Fin 234))
    (h83 : P (83 : Fin 234))
    (h84 : P (84 : Fin 234))
    (h85 : P (85 : Fin 234))
    (h86 : P (86 : Fin 234))
    (h87 : P (87 : Fin 234))
    (h88 : P (88 : Fin 234))
    (h89 : P (89 : Fin 234))
    (h90 : P (90 : Fin 234))
    (h91 : P (91 : Fin 234))
    (h92 : P (92 : Fin 234))
    (h93 : P (93 : Fin 234))
    (h94 : P (94 : Fin 234))
    (h95 : P (95 : Fin 234))
    (h96 : P (96 : Fin 234))
    (h97 : P (97 : Fin 234))
    (h98 : P (98 : Fin 234))
    (h99 : P (99 : Fin 234))
    (h100 : P (100 : Fin 234))
    (h101 : P (101 : Fin 234))
    (h102 : P (102 : Fin 234))
    (h103 : P (103 : Fin 234))
    (h104 : P (104 : Fin 234))
    (h105 : P (105 : Fin 234))
    (h106 : P (106 : Fin 234))
    (h107 : P (107 : Fin 234))
    (h108 : P (108 : Fin 234))
    (h109 : P (109 : Fin 234))
    (h110 : P (110 : Fin 234))
    (h111 : P (111 : Fin 234))
    (h112 : P (112 : Fin 234))
    (h113 : P (113 : Fin 234))
    (h114 : P (114 : Fin 234))
    (h115 : P (115 : Fin 234))
    (h116 : P (116 : Fin 234))
    (h117 : P (117 : Fin 234))
    (h118 : P (118 : Fin 234))
    (h119 : P (119 : Fin 234))
    (h120 : P (120 : Fin 234))
    (h121 : P (121 : Fin 234))
    (h122 : P (122 : Fin 234))
    (h123 : P (123 : Fin 234))
    (h124 : P (124 : Fin 234))
    (h125 : P (125 : Fin 234))
    (h126 : P (126 : Fin 234))
    (h127 : P (127 : Fin 234))
    (h128 : P (128 : Fin 234))
    (h129 : P (129 : Fin 234))
    (h130 : P (130 : Fin 234))
    (h131 : P (131 : Fin 234))
    (h132 : P (132 : Fin 234))
    (h133 : P (133 : Fin 234))
    (h134 : P (134 : Fin 234))
    (h135 : P (135 : Fin 234))
    (h136 : P (136 : Fin 234))
    (h137 : P (137 : Fin 234))
    (h138 : P (138 : Fin 234))
    (h139 : P (139 : Fin 234))
    (h140 : P (140 : Fin 234))
    (h141 : P (141 : Fin 234))
    (h142 : P (142 : Fin 234))
    (h143 : P (143 : Fin 234))
    (h144 : P (144 : Fin 234))
    (h145 : P (145 : Fin 234))
    (h146 : P (146 : Fin 234))
    (h147 : P (147 : Fin 234))
    (h148 : P (148 : Fin 234))
    (h149 : P (149 : Fin 234))
    (h150 : P (150 : Fin 234))
    (h151 : P (151 : Fin 234))
    (h152 : P (152 : Fin 234))
    (h153 : P (153 : Fin 234))
    (h154 : P (154 : Fin 234))
    (h155 : P (155 : Fin 234))
    (h156 : P (156 : Fin 234))
    (h157 : P (157 : Fin 234))
    (h158 : P (158 : Fin 234))
    (h159 : P (159 : Fin 234))
    (h160 : P (160 : Fin 234))
    (h161 : P (161 : Fin 234))
    (h162 : P (162 : Fin 234))
    (h163 : P (163 : Fin 234))
    (h164 : P (164 : Fin 234))
    (h165 : P (165 : Fin 234))
    (h166 : P (166 : Fin 234))
    (h167 : P (167 : Fin 234))
    (h168 : P (168 : Fin 234))
    (h169 : P (169 : Fin 234))
    (h170 : P (170 : Fin 234))
    (h171 : P (171 : Fin 234))
    (h172 : P (172 : Fin 234))
    (h173 : P (173 : Fin 234))
    (h174 : P (174 : Fin 234))
    (h175 : P (175 : Fin 234))
    (h176 : P (176 : Fin 234))
    (h177 : P (177 : Fin 234))
    (h178 : P (178 : Fin 234))
    (h179 : P (179 : Fin 234))
    (h180 : P (180 : Fin 234))
    (h181 : P (181 : Fin 234))
    (h182 : P (182 : Fin 234))
    (h183 : P (183 : Fin 234))
    (h184 : P (184 : Fin 234))
    (h185 : P (185 : Fin 234))
    (h186 : P (186 : Fin 234))
    (h187 : P (187 : Fin 234))
    (h188 : P (188 : Fin 234))
    (h189 : P (189 : Fin 234))
    (h190 : P (190 : Fin 234))
    (h191 : P (191 : Fin 234))
    (h192 : P (192 : Fin 234))
    (h193 : P (193 : Fin 234))
    (h194 : P (194 : Fin 234))
    (h195 : P (195 : Fin 234))
    (h196 : P (196 : Fin 234))
    (h197 : P (197 : Fin 234))
    (h198 : P (198 : Fin 234))
    (h199 : P (199 : Fin 234))
    (h200 : P (200 : Fin 234))
    (h201 : P (201 : Fin 234))
    (h202 : P (202 : Fin 234))
    (h203 : P (203 : Fin 234))
    (h204 : P (204 : Fin 234))
    (h205 : P (205 : Fin 234))
    (h206 : P (206 : Fin 234))
    (h207 : P (207 : Fin 234))
    (h208 : P (208 : Fin 234))
    (h209 : P (209 : Fin 234))
    (h210 : P (210 : Fin 234))
    (h211 : P (211 : Fin 234))
    (h212 : P (212 : Fin 234))
    (h213 : P (213 : Fin 234))
    (h214 : P (214 : Fin 234))
    (h215 : P (215 : Fin 234))
    (h216 : P (216 : Fin 234))
    (h217 : P (217 : Fin 234))
    (h218 : P (218 : Fin 234))
    (h219 : P (219 : Fin 234))
    (h220 : P (220 : Fin 234))
    (h221 : P (221 : Fin 234))
    (h222 : P (222 : Fin 234))
    (h223 : P (223 : Fin 234))
    (h224 : P (224 : Fin 234))
    (h225 : P (225 : Fin 234))
    (h226 : P (226 : Fin 234))
    (h227 : P (227 : Fin 234))
    (h228 : P (228 : Fin 234))
    (h229 : P (229 : Fin 234))
    (h230 : P (230 : Fin 234))
    (h231 : P (231 : Fin 234))
    (h232 : P (232 : Fin 234))
    (h233 : P (233 : Fin 234))
    (i : Fin 234) : P i := by
  exact @Fin.cases 233 P h0 (@Fin.cases 232 (fun j : Fin 233 => P (j.addNat 1)) h1 (@Fin.cases 231 (fun j : Fin 232 => P (j.addNat 2)) h2 (@Fin.cases 230 (fun j : Fin 231 => P (j.addNat 3)) h3 (@Fin.cases 229 (fun j : Fin 230 => P (j.addNat 4)) h4 (@Fin.cases 228 (fun j : Fin 229 => P (j.addNat 5)) h5 (@Fin.cases 227 (fun j : Fin 228 => P (j.addNat 6)) h6 (@Fin.cases 226 (fun j : Fin 227 => P (j.addNat 7)) h7 (@Fin.cases 225 (fun j : Fin 226 => P (j.addNat 8)) h8 (@Fin.cases 224 (fun j : Fin 225 => P (j.addNat 9)) h9 (@Fin.cases 223 (fun j : Fin 224 => P (j.addNat 10)) h10 (@Fin.cases 222 (fun j : Fin 223 => P (j.addNat 11)) h11 (@Fin.cases 221 (fun j : Fin 222 => P (j.addNat 12)) h12 (@Fin.cases 220 (fun j : Fin 221 => P (j.addNat 13)) h13 (@Fin.cases 219 (fun j : Fin 220 => P (j.addNat 14)) h14 (@Fin.cases 218 (fun j : Fin 219 => P (j.addNat 15)) h15 (@Fin.cases 217 (fun j : Fin 218 => P (j.addNat 16)) h16 (@Fin.cases 216 (fun j : Fin 217 => P (j.addNat 17)) h17 (@Fin.cases 215 (fun j : Fin 216 => P (j.addNat 18)) h18 (@Fin.cases 214 (fun j : Fin 215 => P (j.addNat 19)) h19 (@Fin.cases 213 (fun j : Fin 214 => P (j.addNat 20)) h20 (@Fin.cases 212 (fun j : Fin 213 => P (j.addNat 21)) h21 (@Fin.cases 211 (fun j : Fin 212 => P (j.addNat 22)) h22 (@Fin.cases 210 (fun j : Fin 211 => P (j.addNat 23)) h23 (@Fin.cases 209 (fun j : Fin 210 => P (j.addNat 24)) h24 (@Fin.cases 208 (fun j : Fin 209 => P (j.addNat 25)) h25 (@Fin.cases 207 (fun j : Fin 208 => P (j.addNat 26)) h26 (@Fin.cases 206 (fun j : Fin 207 => P (j.addNat 27)) h27 (@Fin.cases 205 (fun j : Fin 206 => P (j.addNat 28)) h28 (@Fin.cases 204 (fun j : Fin 205 => P (j.addNat 29)) h29 (@Fin.cases 203 (fun j : Fin 204 => P (j.addNat 30)) h30 (@Fin.cases 202 (fun j : Fin 203 => P (j.addNat 31)) h31 (@Fin.cases 201 (fun j : Fin 202 => P (j.addNat 32)) h32 (@Fin.cases 200 (fun j : Fin 201 => P (j.addNat 33)) h33 (@Fin.cases 199 (fun j : Fin 200 => P (j.addNat 34)) h34 (@Fin.cases 198 (fun j : Fin 199 => P (j.addNat 35)) h35 (@Fin.cases 197 (fun j : Fin 198 => P (j.addNat 36)) h36 (@Fin.cases 196 (fun j : Fin 197 => P (j.addNat 37)) h37 (@Fin.cases 195 (fun j : Fin 196 => P (j.addNat 38)) h38 (@Fin.cases 194 (fun j : Fin 195 => P (j.addNat 39)) h39 (@Fin.cases 193 (fun j : Fin 194 => P (j.addNat 40)) h40 (@Fin.cases 192 (fun j : Fin 193 => P (j.addNat 41)) h41 (@Fin.cases 191 (fun j : Fin 192 => P (j.addNat 42)) h42 (@Fin.cases 190 (fun j : Fin 191 => P (j.addNat 43)) h43 (@Fin.cases 189 (fun j : Fin 190 => P (j.addNat 44)) h44 (@Fin.cases 188 (fun j : Fin 189 => P (j.addNat 45)) h45 (@Fin.cases 187 (fun j : Fin 188 => P (j.addNat 46)) h46 (@Fin.cases 186 (fun j : Fin 187 => P (j.addNat 47)) h47 (@Fin.cases 185 (fun j : Fin 186 => P (j.addNat 48)) h48 (@Fin.cases 184 (fun j : Fin 185 => P (j.addNat 49)) h49 (@Fin.cases 183 (fun j : Fin 184 => P (j.addNat 50)) h50 (@Fin.cases 182 (fun j : Fin 183 => P (j.addNat 51)) h51 (@Fin.cases 181 (fun j : Fin 182 => P (j.addNat 52)) h52 (@Fin.cases 180 (fun j : Fin 181 => P (j.addNat 53)) h53 (@Fin.cases 179 (fun j : Fin 180 => P (j.addNat 54)) h54 (@Fin.cases 178 (fun j : Fin 179 => P (j.addNat 55)) h55 (@Fin.cases 177 (fun j : Fin 178 => P (j.addNat 56)) h56 (@Fin.cases 176 (fun j : Fin 177 => P (j.addNat 57)) h57 (@Fin.cases 175 (fun j : Fin 176 => P (j.addNat 58)) h58 (@Fin.cases 174 (fun j : Fin 175 => P (j.addNat 59)) h59 (@Fin.cases 173 (fun j : Fin 174 => P (j.addNat 60)) h60 (@Fin.cases 172 (fun j : Fin 173 => P (j.addNat 61)) h61 (@Fin.cases 171 (fun j : Fin 172 => P (j.addNat 62)) h62 (@Fin.cases 170 (fun j : Fin 171 => P (j.addNat 63)) h63 (@Fin.cases 169 (fun j : Fin 170 => P (j.addNat 64)) h64 (@Fin.cases 168 (fun j : Fin 169 => P (j.addNat 65)) h65 (@Fin.cases 167 (fun j : Fin 168 => P (j.addNat 66)) h66 (@Fin.cases 166 (fun j : Fin 167 => P (j.addNat 67)) h67 (@Fin.cases 165 (fun j : Fin 166 => P (j.addNat 68)) h68 (@Fin.cases 164 (fun j : Fin 165 => P (j.addNat 69)) h69 (@Fin.cases 163 (fun j : Fin 164 => P (j.addNat 70)) h70 (@Fin.cases 162 (fun j : Fin 163 => P (j.addNat 71)) h71 (@Fin.cases 161 (fun j : Fin 162 => P (j.addNat 72)) h72 (@Fin.cases 160 (fun j : Fin 161 => P (j.addNat 73)) h73 (@Fin.cases 159 (fun j : Fin 160 => P (j.addNat 74)) h74 (@Fin.cases 158 (fun j : Fin 159 => P (j.addNat 75)) h75 (@Fin.cases 157 (fun j : Fin 158 => P (j.addNat 76)) h76 (@Fin.cases 156 (fun j : Fin 157 => P (j.addNat 77)) h77 (@Fin.cases 155 (fun j : Fin 156 => P (j.addNat 78)) h78 (@Fin.cases 154 (fun j : Fin 155 => P (j.addNat 79)) h79 (@Fin.cases 153 (fun j : Fin 154 => P (j.addNat 80)) h80 (@Fin.cases 152 (fun j : Fin 153 => P (j.addNat 81)) h81 (@Fin.cases 151 (fun j : Fin 152 => P (j.addNat 82)) h82 (@Fin.cases 150 (fun j : Fin 151 => P (j.addNat 83)) h83 (@Fin.cases 149 (fun j : Fin 150 => P (j.addNat 84)) h84 (@Fin.cases 148 (fun j : Fin 149 => P (j.addNat 85)) h85 (@Fin.cases 147 (fun j : Fin 148 => P (j.addNat 86)) h86 (@Fin.cases 146 (fun j : Fin 147 => P (j.addNat 87)) h87 (@Fin.cases 145 (fun j : Fin 146 => P (j.addNat 88)) h88 (@Fin.cases 144 (fun j : Fin 145 => P (j.addNat 89)) h89 (@Fin.cases 143 (fun j : Fin 144 => P (j.addNat 90)) h90 (@Fin.cases 142 (fun j : Fin 143 => P (j.addNat 91)) h91 (@Fin.cases 141 (fun j : Fin 142 => P (j.addNat 92)) h92 (@Fin.cases 140 (fun j : Fin 141 => P (j.addNat 93)) h93 (@Fin.cases 139 (fun j : Fin 140 => P (j.addNat 94)) h94 (@Fin.cases 138 (fun j : Fin 139 => P (j.addNat 95)) h95 (@Fin.cases 137 (fun j : Fin 138 => P (j.addNat 96)) h96 (@Fin.cases 136 (fun j : Fin 137 => P (j.addNat 97)) h97 (@Fin.cases 135 (fun j : Fin 136 => P (j.addNat 98)) h98 (@Fin.cases 134 (fun j : Fin 135 => P (j.addNat 99)) h99 (@Fin.cases 133 (fun j : Fin 134 => P (j.addNat 100)) h100 (@Fin.cases 132 (fun j : Fin 133 => P (j.addNat 101)) h101 (@Fin.cases 131 (fun j : Fin 132 => P (j.addNat 102)) h102 (@Fin.cases 130 (fun j : Fin 131 => P (j.addNat 103)) h103 (@Fin.cases 129 (fun j : Fin 130 => P (j.addNat 104)) h104 (@Fin.cases 128 (fun j : Fin 129 => P (j.addNat 105)) h105 (@Fin.cases 127 (fun j : Fin 128 => P (j.addNat 106)) h106 (@Fin.cases 126 (fun j : Fin 127 => P (j.addNat 107)) h107 (@Fin.cases 125 (fun j : Fin 126 => P (j.addNat 108)) h108 (@Fin.cases 124 (fun j : Fin 125 => P (j.addNat 109)) h109 (@Fin.cases 123 (fun j : Fin 124 => P (j.addNat 110)) h110 (@Fin.cases 122 (fun j : Fin 123 => P (j.addNat 111)) h111 (@Fin.cases 121 (fun j : Fin 122 => P (j.addNat 112)) h112 (@Fin.cases 120 (fun j : Fin 121 => P (j.addNat 113)) h113 (@Fin.cases 119 (fun j : Fin 120 => P (j.addNat 114)) h114 (@Fin.cases 118 (fun j : Fin 119 => P (j.addNat 115)) h115 (@Fin.cases 117 (fun j : Fin 118 => P (j.addNat 116)) h116 (@Fin.cases 116 (fun j : Fin 117 => P (j.addNat 117)) h117 (@Fin.cases 115 (fun j : Fin 116 => P (j.addNat 118)) h118 (@Fin.cases 114 (fun j : Fin 115 => P (j.addNat 119)) h119 (@Fin.cases 113 (fun j : Fin 114 => P (j.addNat 120)) h120 (@Fin.cases 112 (fun j : Fin 113 => P (j.addNat 121)) h121 (@Fin.cases 111 (fun j : Fin 112 => P (j.addNat 122)) h122 (@Fin.cases 110 (fun j : Fin 111 => P (j.addNat 123)) h123 (@Fin.cases 109 (fun j : Fin 110 => P (j.addNat 124)) h124 (@Fin.cases 108 (fun j : Fin 109 => P (j.addNat 125)) h125 (@Fin.cases 107 (fun j : Fin 108 => P (j.addNat 126)) h126 (@Fin.cases 106 (fun j : Fin 107 => P (j.addNat 127)) h127 (@Fin.cases 105 (fun j : Fin 106 => P (j.addNat 128)) h128 (@Fin.cases 104 (fun j : Fin 105 => P (j.addNat 129)) h129 (@Fin.cases 103 (fun j : Fin 104 => P (j.addNat 130)) h130 (@Fin.cases 102 (fun j : Fin 103 => P (j.addNat 131)) h131 (@Fin.cases 101 (fun j : Fin 102 => P (j.addNat 132)) h132 (@Fin.cases 100 (fun j : Fin 101 => P (j.addNat 133)) h133 (@Fin.cases 99 (fun j : Fin 100 => P (j.addNat 134)) h134 (@Fin.cases 98 (fun j : Fin 99 => P (j.addNat 135)) h135 (@Fin.cases 97 (fun j : Fin 98 => P (j.addNat 136)) h136 (@Fin.cases 96 (fun j : Fin 97 => P (j.addNat 137)) h137 (@Fin.cases 95 (fun j : Fin 96 => P (j.addNat 138)) h138 (@Fin.cases 94 (fun j : Fin 95 => P (j.addNat 139)) h139 (@Fin.cases 93 (fun j : Fin 94 => P (j.addNat 140)) h140 (@Fin.cases 92 (fun j : Fin 93 => P (j.addNat 141)) h141 (@Fin.cases 91 (fun j : Fin 92 => P (j.addNat 142)) h142 (@Fin.cases 90 (fun j : Fin 91 => P (j.addNat 143)) h143 (@Fin.cases 89 (fun j : Fin 90 => P (j.addNat 144)) h144 (@Fin.cases 88 (fun j : Fin 89 => P (j.addNat 145)) h145 (@Fin.cases 87 (fun j : Fin 88 => P (j.addNat 146)) h146 (@Fin.cases 86 (fun j : Fin 87 => P (j.addNat 147)) h147 (@Fin.cases 85 (fun j : Fin 86 => P (j.addNat 148)) h148 (@Fin.cases 84 (fun j : Fin 85 => P (j.addNat 149)) h149 (@Fin.cases 83 (fun j : Fin 84 => P (j.addNat 150)) h150 (@Fin.cases 82 (fun j : Fin 83 => P (j.addNat 151)) h151 (@Fin.cases 81 (fun j : Fin 82 => P (j.addNat 152)) h152 (@Fin.cases 80 (fun j : Fin 81 => P (j.addNat 153)) h153 (@Fin.cases 79 (fun j : Fin 80 => P (j.addNat 154)) h154 (@Fin.cases 78 (fun j : Fin 79 => P (j.addNat 155)) h155 (@Fin.cases 77 (fun j : Fin 78 => P (j.addNat 156)) h156 (@Fin.cases 76 (fun j : Fin 77 => P (j.addNat 157)) h157 (@Fin.cases 75 (fun j : Fin 76 => P (j.addNat 158)) h158 (@Fin.cases 74 (fun j : Fin 75 => P (j.addNat 159)) h159 (@Fin.cases 73 (fun j : Fin 74 => P (j.addNat 160)) h160 (@Fin.cases 72 (fun j : Fin 73 => P (j.addNat 161)) h161 (@Fin.cases 71 (fun j : Fin 72 => P (j.addNat 162)) h162 (@Fin.cases 70 (fun j : Fin 71 => P (j.addNat 163)) h163 (@Fin.cases 69 (fun j : Fin 70 => P (j.addNat 164)) h164 (@Fin.cases 68 (fun j : Fin 69 => P (j.addNat 165)) h165 (@Fin.cases 67 (fun j : Fin 68 => P (j.addNat 166)) h166 (@Fin.cases 66 (fun j : Fin 67 => P (j.addNat 167)) h167 (@Fin.cases 65 (fun j : Fin 66 => P (j.addNat 168)) h168 (@Fin.cases 64 (fun j : Fin 65 => P (j.addNat 169)) h169 (@Fin.cases 63 (fun j : Fin 64 => P (j.addNat 170)) h170 (@Fin.cases 62 (fun j : Fin 63 => P (j.addNat 171)) h171 (@Fin.cases 61 (fun j : Fin 62 => P (j.addNat 172)) h172 (@Fin.cases 60 (fun j : Fin 61 => P (j.addNat 173)) h173 (@Fin.cases 59 (fun j : Fin 60 => P (j.addNat 174)) h174 (@Fin.cases 58 (fun j : Fin 59 => P (j.addNat 175)) h175 (@Fin.cases 57 (fun j : Fin 58 => P (j.addNat 176)) h176 (@Fin.cases 56 (fun j : Fin 57 => P (j.addNat 177)) h177 (@Fin.cases 55 (fun j : Fin 56 => P (j.addNat 178)) h178 (@Fin.cases 54 (fun j : Fin 55 => P (j.addNat 179)) h179 (@Fin.cases 53 (fun j : Fin 54 => P (j.addNat 180)) h180 (@Fin.cases 52 (fun j : Fin 53 => P (j.addNat 181)) h181 (@Fin.cases 51 (fun j : Fin 52 => P (j.addNat 182)) h182 (@Fin.cases 50 (fun j : Fin 51 => P (j.addNat 183)) h183 (@Fin.cases 49 (fun j : Fin 50 => P (j.addNat 184)) h184 (@Fin.cases 48 (fun j : Fin 49 => P (j.addNat 185)) h185 (@Fin.cases 47 (fun j : Fin 48 => P (j.addNat 186)) h186 (@Fin.cases 46 (fun j : Fin 47 => P (j.addNat 187)) h187 (@Fin.cases 45 (fun j : Fin 46 => P (j.addNat 188)) h188 (@Fin.cases 44 (fun j : Fin 45 => P (j.addNat 189)) h189 (@Fin.cases 43 (fun j : Fin 44 => P (j.addNat 190)) h190 (@Fin.cases 42 (fun j : Fin 43 => P (j.addNat 191)) h191 (@Fin.cases 41 (fun j : Fin 42 => P (j.addNat 192)) h192 (@Fin.cases 40 (fun j : Fin 41 => P (j.addNat 193)) h193 (@Fin.cases 39 (fun j : Fin 40 => P (j.addNat 194)) h194 (@Fin.cases 38 (fun j : Fin 39 => P (j.addNat 195)) h195 (@Fin.cases 37 (fun j : Fin 38 => P (j.addNat 196)) h196 (@Fin.cases 36 (fun j : Fin 37 => P (j.addNat 197)) h197 (@Fin.cases 35 (fun j : Fin 36 => P (j.addNat 198)) h198 (@Fin.cases 34 (fun j : Fin 35 => P (j.addNat 199)) h199 (@Fin.cases 33 (fun j : Fin 34 => P (j.addNat 200)) h200 (@Fin.cases 32 (fun j : Fin 33 => P (j.addNat 201)) h201 (@Fin.cases 31 (fun j : Fin 32 => P (j.addNat 202)) h202 (@Fin.cases 30 (fun j : Fin 31 => P (j.addNat 203)) h203 (@Fin.cases 29 (fun j : Fin 30 => P (j.addNat 204)) h204 (@Fin.cases 28 (fun j : Fin 29 => P (j.addNat 205)) h205 (@Fin.cases 27 (fun j : Fin 28 => P (j.addNat 206)) h206 (@Fin.cases 26 (fun j : Fin 27 => P (j.addNat 207)) h207 (@Fin.cases 25 (fun j : Fin 26 => P (j.addNat 208)) h208 (@Fin.cases 24 (fun j : Fin 25 => P (j.addNat 209)) h209 (@Fin.cases 23 (fun j : Fin 24 => P (j.addNat 210)) h210 (@Fin.cases 22 (fun j : Fin 23 => P (j.addNat 211)) h211 (@Fin.cases 21 (fun j : Fin 22 => P (j.addNat 212)) h212 (@Fin.cases 20 (fun j : Fin 21 => P (j.addNat 213)) h213 (@Fin.cases 19 (fun j : Fin 20 => P (j.addNat 214)) h214 (@Fin.cases 18 (fun j : Fin 19 => P (j.addNat 215)) h215 (@Fin.cases 17 (fun j : Fin 18 => P (j.addNat 216)) h216 (@Fin.cases 16 (fun j : Fin 17 => P (j.addNat 217)) h217 (@Fin.cases 15 (fun j : Fin 16 => P (j.addNat 218)) h218 (@Fin.cases 14 (fun j : Fin 15 => P (j.addNat 219)) h219 (@Fin.cases 13 (fun j : Fin 14 => P (j.addNat 220)) h220 (@Fin.cases 12 (fun j : Fin 13 => P (j.addNat 221)) h221 (@Fin.cases 11 (fun j : Fin 12 => P (j.addNat 222)) h222 (@Fin.cases 10 (fun j : Fin 11 => P (j.addNat 223)) h223 (@Fin.cases 9 (fun j : Fin 10 => P (j.addNat 224)) h224 (@Fin.cases 8 (fun j : Fin 9 => P (j.addNat 225)) h225 (@Fin.cases 7 (fun j : Fin 8 => P (j.addNat 226)) h226 (@Fin.cases 6 (fun j : Fin 7 => P (j.addNat 227)) h227 (@Fin.cases 5 (fun j : Fin 6 => P (j.addNat 228)) h228 (@Fin.cases 4 (fun j : Fin 5 => P (j.addNat 229)) h229 (@Fin.cases 3 (fun j : Fin 4 => P (j.addNat 230)) h230 (@Fin.cases 2 (fun j : Fin 3 => P (j.addNat 231)) h231 (@Fin.cases 1 (fun j : Fin 2 => P (j.addNat 232)) h232 (@Fin.cases 0 (fun j : Fin 1 => P (j.addNat 233)) h233 ((fun j : Fin 0 => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) i

theorem bulkNearVertex_cases_0 (P : Fin 234 → Prop)
    (h0 : P (0 : Fin 234))
    (h1 : P (1 : Fin 234))
    (h2 : P (2 : Fin 234))
    (h3 : P (3 : Fin 234))
    (h4 : P (4 : Fin 234))
    (h5 : P (5 : Fin 234))
    (h6 : P (6 : Fin 234))
    (h7 : P (7 : Fin 234))
    (h8 : P (8 : Fin 234))
    (h9 : P (9 : Fin 234))
    (h10 : P (10 : Fin 234))
    (h11 : P (11 : Fin 234))
    (h12 : P (12 : Fin 234))
    (h13 : P (13 : Fin 234))
    (i : Fin 234) (hv : bulkNearSegmentVertex i = 0) : P i := by
  refine bulkNearAllIndices_cases (fun j => bulkNearSegmentVertex j = 0 → P j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hv
  · intro _; exact h0
  · intro _; exact h1
  · intro _; exact h2
  · intro _; exact h3
  · intro _; exact h4
  · intro _; exact h5
  · intro _; exact h6
  · intro _; exact h7
  · intro _; exact h8
  · intro _; exact h9
  · intro _; exact h10
  · intro _; exact h11
  · intro _; exact h12
  · intro _; exact h13
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_14.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_15.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_16.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_17.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_18.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_19.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_20.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_21.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_22.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_23.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_24.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_25.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_26.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_27.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_28.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_29.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_30.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_31.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_32.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_33.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_34.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_35.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_36.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_37.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_38.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_39.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_40.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_41.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_42.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_43.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_44.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_45.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_46.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_47.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_48.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_49.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_50.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_51.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_52.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_53.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_54.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_55.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_56.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_57.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_58.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_59.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_60.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_61.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_62.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_63.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_64.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_65.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_66.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_67.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_68.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_69.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_70.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_71.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_72.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_73.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_74.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_75.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_76.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_77.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_78.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_79.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_80.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_81.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_82.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_83.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_84.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_85.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_86.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_87.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_88.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_89.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_90.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_91.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_92.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_93.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_94.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_95.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_96.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_97.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_98.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_99.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_100.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_101.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_102.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_103.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_104.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_105.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_106.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_107.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_108.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_109.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_110.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_111.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_112.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_113.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_114.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_115.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_116.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_117.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_118.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_119.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_120.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_121.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_122.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_123.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_124.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_125.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_126.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_127.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_128.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_129.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_130.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_131.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_132.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_133.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_134.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_135.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_136.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_137.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_138.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_139.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_140.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_141.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_142.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_143.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_144.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_145.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_146.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_147.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_148.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_149.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_150.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_151.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_152.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_153.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_154.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_155.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_156.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_157.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_158.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_159.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_160.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_161.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_162.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_163.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_164.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_165.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_166.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_167.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_168.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_169.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_170.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_171.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_172.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_173.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_174.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_175.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_176.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_177.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_178.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_179.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_180.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_181.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_182.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_183.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_184.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_185.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_186.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_187.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_188.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_189.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_190.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_191.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_192.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_193.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_194.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_195.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_196.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_197.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_198.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_199.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_200.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_201.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_202.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_203.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_204.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_205.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_206.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_207.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_208.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_209.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_210.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_211.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_212.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_213.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_214.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_215.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_216.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_217.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_218.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_219.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_220.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_221.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_222.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_223.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_224.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_225.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_226.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_227.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_228.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_229.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_230.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_231.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_232.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (0 : Fin 6))
      (bulkNearVertex_value_233.symm.trans hj))

theorem bulkNearVertex_cases_1 (P : Fin 234 → Prop)
    (h14 : P (14 : Fin 234))
    (h15 : P (15 : Fin 234))
    (h16 : P (16 : Fin 234))
    (h17 : P (17 : Fin 234))
    (h18 : P (18 : Fin 234))
    (h19 : P (19 : Fin 234))
    (h20 : P (20 : Fin 234))
    (h21 : P (21 : Fin 234))
    (h22 : P (22 : Fin 234))
    (h23 : P (23 : Fin 234))
    (h24 : P (24 : Fin 234))
    (h25 : P (25 : Fin 234))
    (h26 : P (26 : Fin 234))
    (h27 : P (27 : Fin 234))
    (h28 : P (28 : Fin 234))
    (h29 : P (29 : Fin 234))
    (h30 : P (30 : Fin 234))
    (h31 : P (31 : Fin 234))
    (h32 : P (32 : Fin 234))
    (h33 : P (33 : Fin 234))
    (h34 : P (34 : Fin 234))
    (h35 : P (35 : Fin 234))
    (h36 : P (36 : Fin 234))
    (h37 : P (37 : Fin 234))
    (h38 : P (38 : Fin 234))
    (h39 : P (39 : Fin 234))
    (h40 : P (40 : Fin 234))
    (h41 : P (41 : Fin 234))
    (h42 : P (42 : Fin 234))
    (h43 : P (43 : Fin 234))
    (h44 : P (44 : Fin 234))
    (h45 : P (45 : Fin 234))
    (h46 : P (46 : Fin 234))
    (h47 : P (47 : Fin 234))
    (h48 : P (48 : Fin 234))
    (h49 : P (49 : Fin 234))
    (h50 : P (50 : Fin 234))
    (h51 : P (51 : Fin 234))
    (h52 : P (52 : Fin 234))
    (h53 : P (53 : Fin 234))
    (h54 : P (54 : Fin 234))
    (h55 : P (55 : Fin 234))
    (h56 : P (56 : Fin 234))
    (h57 : P (57 : Fin 234))
    (h58 : P (58 : Fin 234))
    (h59 : P (59 : Fin 234))
    (h60 : P (60 : Fin 234))
    (h61 : P (61 : Fin 234))
    (h62 : P (62 : Fin 234))
    (h63 : P (63 : Fin 234))
    (h64 : P (64 : Fin 234))
    (h65 : P (65 : Fin 234))
    (h66 : P (66 : Fin 234))
    (h67 : P (67 : Fin 234))
    (h68 : P (68 : Fin 234))
    (i : Fin 234) (hv : bulkNearSegmentVertex i = 1) : P i := by
  refine bulkNearAllIndices_cases (fun j => bulkNearSegmentVertex j = 1 → P j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hv
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_0.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_1.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_2.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_3.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_4.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_5.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_6.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_7.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_8.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_9.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_10.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_11.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_12.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_13.symm.trans hj))
  · intro _; exact h14
  · intro _; exact h15
  · intro _; exact h16
  · intro _; exact h17
  · intro _; exact h18
  · intro _; exact h19
  · intro _; exact h20
  · intro _; exact h21
  · intro _; exact h22
  · intro _; exact h23
  · intro _; exact h24
  · intro _; exact h25
  · intro _; exact h26
  · intro _; exact h27
  · intro _; exact h28
  · intro _; exact h29
  · intro _; exact h30
  · intro _; exact h31
  · intro _; exact h32
  · intro _; exact h33
  · intro _; exact h34
  · intro _; exact h35
  · intro _; exact h36
  · intro _; exact h37
  · intro _; exact h38
  · intro _; exact h39
  · intro _; exact h40
  · intro _; exact h41
  · intro _; exact h42
  · intro _; exact h43
  · intro _; exact h44
  · intro _; exact h45
  · intro _; exact h46
  · intro _; exact h47
  · intro _; exact h48
  · intro _; exact h49
  · intro _; exact h50
  · intro _; exact h51
  · intro _; exact h52
  · intro _; exact h53
  · intro _; exact h54
  · intro _; exact h55
  · intro _; exact h56
  · intro _; exact h57
  · intro _; exact h58
  · intro _; exact h59
  · intro _; exact h60
  · intro _; exact h61
  · intro _; exact h62
  · intro _; exact h63
  · intro _; exact h64
  · intro _; exact h65
  · intro _; exact h66
  · intro _; exact h67
  · intro _; exact h68
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_69.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_70.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_71.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_72.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_73.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_74.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_75.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_76.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_77.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_78.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_79.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_80.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_81.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_82.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_83.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_84.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_85.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_86.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_87.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_88.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_89.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_90.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_91.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_92.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_93.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_94.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_95.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_96.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_97.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_98.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_99.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_100.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_101.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_102.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_103.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_104.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_105.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_106.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_107.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_108.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_109.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_110.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_111.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_112.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_113.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_114.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_115.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_116.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_117.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_118.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_119.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_120.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_121.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_122.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_123.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_124.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_125.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_126.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_127.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_128.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_129.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_130.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_131.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_132.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_133.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_134.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_135.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_136.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_137.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_138.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_139.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_140.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_141.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_142.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_143.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_144.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_145.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_146.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_147.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_148.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_149.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_150.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_151.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_152.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_153.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_154.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_155.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_156.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_157.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_158.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_159.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_160.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_161.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_162.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_163.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_164.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_165.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_166.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_167.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_168.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_169.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_170.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_171.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_172.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_173.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_174.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_175.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_176.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_177.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_178.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_179.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_180.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_181.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_182.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_183.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_184.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_185.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_186.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_187.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_188.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_189.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_190.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_191.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_192.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_193.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_194.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_195.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_196.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_197.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_198.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_199.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_200.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_201.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_202.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_203.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_204.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_205.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_206.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_207.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_208.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_209.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_210.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_211.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_212.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_213.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_214.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_215.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_216.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_217.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_218.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_219.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_220.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_221.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_222.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_223.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_224.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_225.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_226.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_227.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_228.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_229.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_230.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_231.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_232.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (1 : Fin 6))
      (bulkNearVertex_value_233.symm.trans hj))

theorem bulkNearVertex_cases_2 (P : Fin 234 → Prop)
    (h69 : P (69 : Fin 234))
    (h70 : P (70 : Fin 234))
    (h71 : P (71 : Fin 234))
    (h72 : P (72 : Fin 234))
    (h73 : P (73 : Fin 234))
    (h74 : P (74 : Fin 234))
    (h75 : P (75 : Fin 234))
    (h76 : P (76 : Fin 234))
    (h77 : P (77 : Fin 234))
    (h78 : P (78 : Fin 234))
    (h79 : P (79 : Fin 234))
    (h80 : P (80 : Fin 234))
    (h81 : P (81 : Fin 234))
    (h82 : P (82 : Fin 234))
    (h83 : P (83 : Fin 234))
    (h84 : P (84 : Fin 234))
    (h85 : P (85 : Fin 234))
    (h86 : P (86 : Fin 234))
    (h87 : P (87 : Fin 234))
    (h88 : P (88 : Fin 234))
    (h89 : P (89 : Fin 234))
    (h90 : P (90 : Fin 234))
    (h91 : P (91 : Fin 234))
    (h92 : P (92 : Fin 234))
    (h93 : P (93 : Fin 234))
    (h94 : P (94 : Fin 234))
    (h95 : P (95 : Fin 234))
    (h96 : P (96 : Fin 234))
    (h97 : P (97 : Fin 234))
    (h98 : P (98 : Fin 234))
    (h99 : P (99 : Fin 234))
    (h100 : P (100 : Fin 234))
    (h101 : P (101 : Fin 234))
    (h102 : P (102 : Fin 234))
    (h103 : P (103 : Fin 234))
    (h104 : P (104 : Fin 234))
    (h105 : P (105 : Fin 234))
    (h106 : P (106 : Fin 234))
    (h107 : P (107 : Fin 234))
    (h108 : P (108 : Fin 234))
    (h109 : P (109 : Fin 234))
    (h110 : P (110 : Fin 234))
    (h111 : P (111 : Fin 234))
    (h112 : P (112 : Fin 234))
    (h113 : P (113 : Fin 234))
    (h114 : P (114 : Fin 234))
    (h115 : P (115 : Fin 234))
    (h116 : P (116 : Fin 234))
    (i : Fin 234) (hv : bulkNearSegmentVertex i = 2) : P i := by
  refine bulkNearAllIndices_cases (fun j => bulkNearSegmentVertex j = 2 → P j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hv
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_0.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_1.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_2.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_3.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_4.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_5.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_6.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_7.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_8.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_9.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_10.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_11.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_12.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_13.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_14.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_15.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_16.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_17.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_18.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_19.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_20.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_21.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_22.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_23.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_24.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_25.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_26.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_27.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_28.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_29.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_30.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_31.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_32.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_33.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_34.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_35.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_36.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_37.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_38.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_39.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_40.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_41.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_42.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_43.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_44.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_45.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_46.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_47.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_48.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_49.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_50.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_51.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_52.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_53.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_54.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_55.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_56.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_57.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_58.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_59.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_60.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_61.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_62.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_63.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_64.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_65.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_66.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_67.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_68.symm.trans hj))
  · intro _; exact h69
  · intro _; exact h70
  · intro _; exact h71
  · intro _; exact h72
  · intro _; exact h73
  · intro _; exact h74
  · intro _; exact h75
  · intro _; exact h76
  · intro _; exact h77
  · intro _; exact h78
  · intro _; exact h79
  · intro _; exact h80
  · intro _; exact h81
  · intro _; exact h82
  · intro _; exact h83
  · intro _; exact h84
  · intro _; exact h85
  · intro _; exact h86
  · intro _; exact h87
  · intro _; exact h88
  · intro _; exact h89
  · intro _; exact h90
  · intro _; exact h91
  · intro _; exact h92
  · intro _; exact h93
  · intro _; exact h94
  · intro _; exact h95
  · intro _; exact h96
  · intro _; exact h97
  · intro _; exact h98
  · intro _; exact h99
  · intro _; exact h100
  · intro _; exact h101
  · intro _; exact h102
  · intro _; exact h103
  · intro _; exact h104
  · intro _; exact h105
  · intro _; exact h106
  · intro _; exact h107
  · intro _; exact h108
  · intro _; exact h109
  · intro _; exact h110
  · intro _; exact h111
  · intro _; exact h112
  · intro _; exact h113
  · intro _; exact h114
  · intro _; exact h115
  · intro _; exact h116
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_117.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_118.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_119.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_120.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_121.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_122.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_123.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_124.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_125.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_126.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_127.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_128.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_129.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_130.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_131.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_132.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_133.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_134.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_135.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_136.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_137.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_138.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_139.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_140.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_141.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_142.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_143.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_144.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_145.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_146.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_147.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_148.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_149.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_150.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_151.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_152.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_153.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_154.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_155.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_156.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_157.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_158.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_159.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_160.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_161.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_162.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_163.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_164.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_165.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_166.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_167.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_168.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_169.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_170.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_171.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_172.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_173.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_174.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_175.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_176.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_177.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_178.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_179.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_180.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_181.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_182.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_183.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_184.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_185.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_186.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_187.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_188.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_189.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_190.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_191.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_192.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_193.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_194.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_195.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_196.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_197.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_198.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_199.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_200.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_201.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_202.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_203.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_204.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_205.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_206.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_207.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_208.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_209.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_210.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_211.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_212.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_213.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_214.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_215.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_216.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_217.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_218.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_219.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_220.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_221.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_222.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_223.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_224.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_225.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_226.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_227.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_228.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_229.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_230.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_231.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_232.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (2 : Fin 6))
      (bulkNearVertex_value_233.symm.trans hj))

theorem bulkNearVertex_cases_3 (P : Fin 234 → Prop)
    (h117 : P (117 : Fin 234))
    (h118 : P (118 : Fin 234))
    (h119 : P (119 : Fin 234))
    (h120 : P (120 : Fin 234))
    (h121 : P (121 : Fin 234))
    (h122 : P (122 : Fin 234))
    (h123 : P (123 : Fin 234))
    (h124 : P (124 : Fin 234))
    (h125 : P (125 : Fin 234))
    (h126 : P (126 : Fin 234))
    (h127 : P (127 : Fin 234))
    (h128 : P (128 : Fin 234))
    (h129 : P (129 : Fin 234))
    (h130 : P (130 : Fin 234))
    (h131 : P (131 : Fin 234))
    (h132 : P (132 : Fin 234))
    (h133 : P (133 : Fin 234))
    (h134 : P (134 : Fin 234))
    (h135 : P (135 : Fin 234))
    (h136 : P (136 : Fin 234))
    (h137 : P (137 : Fin 234))
    (h138 : P (138 : Fin 234))
    (h139 : P (139 : Fin 234))
    (h140 : P (140 : Fin 234))
    (h141 : P (141 : Fin 234))
    (h142 : P (142 : Fin 234))
    (h143 : P (143 : Fin 234))
    (h144 : P (144 : Fin 234))
    (h145 : P (145 : Fin 234))
    (h146 : P (146 : Fin 234))
    (h147 : P (147 : Fin 234))
    (h148 : P (148 : Fin 234))
    (h149 : P (149 : Fin 234))
    (h150 : P (150 : Fin 234))
    (h151 : P (151 : Fin 234))
    (h152 : P (152 : Fin 234))
    (h153 : P (153 : Fin 234))
    (h154 : P (154 : Fin 234))
    (h155 : P (155 : Fin 234))
    (h156 : P (156 : Fin 234))
    (h157 : P (157 : Fin 234))
    (h158 : P (158 : Fin 234))
    (h159 : P (159 : Fin 234))
    (h160 : P (160 : Fin 234))
    (h161 : P (161 : Fin 234))
    (h162 : P (162 : Fin 234))
    (h163 : P (163 : Fin 234))
    (h164 : P (164 : Fin 234))
    (i : Fin 234) (hv : bulkNearSegmentVertex i = 3) : P i := by
  refine bulkNearAllIndices_cases (fun j => bulkNearSegmentVertex j = 3 → P j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hv
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_0.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_1.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_2.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_3.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_4.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_5.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_6.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_7.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_8.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_9.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_10.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_11.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_12.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_13.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_14.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_15.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_16.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_17.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_18.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_19.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_20.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_21.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_22.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_23.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_24.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_25.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_26.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_27.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_28.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_29.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_30.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_31.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_32.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_33.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_34.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_35.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_36.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_37.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_38.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_39.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_40.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_41.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_42.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_43.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_44.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_45.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_46.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_47.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_48.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_49.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_50.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_51.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_52.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_53.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_54.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_55.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_56.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_57.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_58.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_59.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_60.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_61.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_62.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_63.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_64.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_65.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_66.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_67.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_68.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_69.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_70.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_71.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_72.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_73.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_74.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_75.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_76.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_77.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_78.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_79.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_80.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_81.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_82.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_83.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_84.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_85.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_86.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_87.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_88.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_89.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_90.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_91.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_92.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_93.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_94.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_95.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_96.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_97.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_98.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_99.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_100.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_101.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_102.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_103.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_104.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_105.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_106.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_107.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_108.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_109.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_110.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_111.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_112.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_113.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_114.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_115.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_116.symm.trans hj))
  · intro _; exact h117
  · intro _; exact h118
  · intro _; exact h119
  · intro _; exact h120
  · intro _; exact h121
  · intro _; exact h122
  · intro _; exact h123
  · intro _; exact h124
  · intro _; exact h125
  · intro _; exact h126
  · intro _; exact h127
  · intro _; exact h128
  · intro _; exact h129
  · intro _; exact h130
  · intro _; exact h131
  · intro _; exact h132
  · intro _; exact h133
  · intro _; exact h134
  · intro _; exact h135
  · intro _; exact h136
  · intro _; exact h137
  · intro _; exact h138
  · intro _; exact h139
  · intro _; exact h140
  · intro _; exact h141
  · intro _; exact h142
  · intro _; exact h143
  · intro _; exact h144
  · intro _; exact h145
  · intro _; exact h146
  · intro _; exact h147
  · intro _; exact h148
  · intro _; exact h149
  · intro _; exact h150
  · intro _; exact h151
  · intro _; exact h152
  · intro _; exact h153
  · intro _; exact h154
  · intro _; exact h155
  · intro _; exact h156
  · intro _; exact h157
  · intro _; exact h158
  · intro _; exact h159
  · intro _; exact h160
  · intro _; exact h161
  · intro _; exact h162
  · intro _; exact h163
  · intro _; exact h164
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_165.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_166.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_167.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_168.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_169.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_170.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_171.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_172.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_173.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_174.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_175.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_176.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_177.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_178.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_179.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_180.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_181.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_182.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_183.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_184.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_185.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_186.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_187.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_188.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_189.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_190.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_191.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_192.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_193.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_194.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_195.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_196.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_197.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_198.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_199.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_200.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_201.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_202.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_203.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_204.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_205.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_206.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_207.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_208.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_209.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_210.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_211.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_212.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_213.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_214.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_215.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_216.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_217.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_218.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_219.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_220.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_221.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_222.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_223.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_224.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_225.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_226.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_227.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_228.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_229.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_230.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_231.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_232.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (3 : Fin 6))
      (bulkNearVertex_value_233.symm.trans hj))

theorem bulkNearVertex_cases_4 (P : Fin 234 → Prop)
    (h165 : P (165 : Fin 234))
    (h166 : P (166 : Fin 234))
    (h167 : P (167 : Fin 234))
    (h168 : P (168 : Fin 234))
    (h169 : P (169 : Fin 234))
    (h170 : P (170 : Fin 234))
    (h171 : P (171 : Fin 234))
    (h172 : P (172 : Fin 234))
    (h173 : P (173 : Fin 234))
    (h174 : P (174 : Fin 234))
    (h175 : P (175 : Fin 234))
    (h176 : P (176 : Fin 234))
    (h177 : P (177 : Fin 234))
    (h178 : P (178 : Fin 234))
    (h179 : P (179 : Fin 234))
    (h180 : P (180 : Fin 234))
    (h181 : P (181 : Fin 234))
    (h182 : P (182 : Fin 234))
    (h183 : P (183 : Fin 234))
    (h184 : P (184 : Fin 234))
    (h185 : P (185 : Fin 234))
    (h186 : P (186 : Fin 234))
    (h187 : P (187 : Fin 234))
    (h188 : P (188 : Fin 234))
    (h189 : P (189 : Fin 234))
    (h190 : P (190 : Fin 234))
    (h191 : P (191 : Fin 234))
    (h192 : P (192 : Fin 234))
    (h193 : P (193 : Fin 234))
    (h194 : P (194 : Fin 234))
    (h195 : P (195 : Fin 234))
    (h196 : P (196 : Fin 234))
    (h197 : P (197 : Fin 234))
    (h198 : P (198 : Fin 234))
    (h199 : P (199 : Fin 234))
    (h200 : P (200 : Fin 234))
    (h201 : P (201 : Fin 234))
    (h202 : P (202 : Fin 234))
    (h203 : P (203 : Fin 234))
    (h204 : P (204 : Fin 234))
    (h205 : P (205 : Fin 234))
    (h206 : P (206 : Fin 234))
    (h207 : P (207 : Fin 234))
    (h208 : P (208 : Fin 234))
    (h209 : P (209 : Fin 234))
    (h210 : P (210 : Fin 234))
    (h211 : P (211 : Fin 234))
    (h212 : P (212 : Fin 234))
    (h213 : P (213 : Fin 234))
    (h214 : P (214 : Fin 234))
    (h215 : P (215 : Fin 234))
    (h216 : P (216 : Fin 234))
    (h217 : P (217 : Fin 234))
    (h218 : P (218 : Fin 234))
    (h219 : P (219 : Fin 234))
    (i : Fin 234) (hv : bulkNearSegmentVertex i = 4) : P i := by
  refine bulkNearAllIndices_cases (fun j => bulkNearSegmentVertex j = 4 → P j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hv
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_0.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_1.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_2.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_3.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_4.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_5.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_6.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_7.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_8.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_9.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_10.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_11.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_12.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_13.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_14.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_15.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_16.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_17.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_18.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_19.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_20.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_21.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_22.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_23.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_24.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_25.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_26.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_27.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_28.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_29.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_30.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_31.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_32.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_33.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_34.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_35.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_36.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_37.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_38.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_39.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_40.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_41.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_42.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_43.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_44.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_45.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_46.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_47.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_48.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_49.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_50.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_51.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_52.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_53.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_54.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_55.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_56.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_57.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_58.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_59.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_60.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_61.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_62.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_63.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_64.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_65.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_66.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_67.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_68.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_69.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_70.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_71.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_72.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_73.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_74.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_75.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_76.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_77.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_78.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_79.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_80.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_81.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_82.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_83.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_84.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_85.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_86.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_87.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_88.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_89.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_90.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_91.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_92.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_93.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_94.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_95.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_96.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_97.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_98.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_99.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_100.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_101.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_102.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_103.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_104.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_105.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_106.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_107.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_108.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_109.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_110.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_111.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_112.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_113.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_114.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_115.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_116.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_117.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_118.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_119.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_120.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_121.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_122.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_123.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_124.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_125.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_126.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_127.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_128.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_129.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_130.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_131.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_132.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_133.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_134.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_135.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_136.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_137.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_138.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_139.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_140.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_141.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_142.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_143.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_144.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_145.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_146.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_147.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_148.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_149.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_150.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_151.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_152.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_153.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_154.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_155.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_156.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_157.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_158.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_159.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_160.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_161.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_162.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_163.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_164.symm.trans hj))
  · intro _; exact h165
  · intro _; exact h166
  · intro _; exact h167
  · intro _; exact h168
  · intro _; exact h169
  · intro _; exact h170
  · intro _; exact h171
  · intro _; exact h172
  · intro _; exact h173
  · intro _; exact h174
  · intro _; exact h175
  · intro _; exact h176
  · intro _; exact h177
  · intro _; exact h178
  · intro _; exact h179
  · intro _; exact h180
  · intro _; exact h181
  · intro _; exact h182
  · intro _; exact h183
  · intro _; exact h184
  · intro _; exact h185
  · intro _; exact h186
  · intro _; exact h187
  · intro _; exact h188
  · intro _; exact h189
  · intro _; exact h190
  · intro _; exact h191
  · intro _; exact h192
  · intro _; exact h193
  · intro _; exact h194
  · intro _; exact h195
  · intro _; exact h196
  · intro _; exact h197
  · intro _; exact h198
  · intro _; exact h199
  · intro _; exact h200
  · intro _; exact h201
  · intro _; exact h202
  · intro _; exact h203
  · intro _; exact h204
  · intro _; exact h205
  · intro _; exact h206
  · intro _; exact h207
  · intro _; exact h208
  · intro _; exact h209
  · intro _; exact h210
  · intro _; exact h211
  · intro _; exact h212
  · intro _; exact h213
  · intro _; exact h214
  · intro _; exact h215
  · intro _; exact h216
  · intro _; exact h217
  · intro _; exact h218
  · intro _; exact h219
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_220.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_221.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_222.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_223.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_224.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_225.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_226.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_227.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_228.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_229.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_230.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_231.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_232.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6))
      (bulkNearVertex_value_233.symm.trans hj))

theorem bulkNearVertex_cases_5 (P : Fin 234 → Prop)
    (h220 : P (220 : Fin 234))
    (h221 : P (221 : Fin 234))
    (h222 : P (222 : Fin 234))
    (h223 : P (223 : Fin 234))
    (h224 : P (224 : Fin 234))
    (h225 : P (225 : Fin 234))
    (h226 : P (226 : Fin 234))
    (h227 : P (227 : Fin 234))
    (h228 : P (228 : Fin 234))
    (h229 : P (229 : Fin 234))
    (h230 : P (230 : Fin 234))
    (h231 : P (231 : Fin 234))
    (h232 : P (232 : Fin 234))
    (h233 : P (233 : Fin 234))
    (i : Fin 234) (hv : bulkNearSegmentVertex i = 5) : P i := by
  refine bulkNearAllIndices_cases (fun j => bulkNearSegmentVertex j = 5 → P j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hv
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_0.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_1.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_2.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_3.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_4.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_5.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_6.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_7.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_8.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_9.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_10.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_11.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_12.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (0 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_13.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_14.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_15.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_16.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_17.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_18.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_19.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_20.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_21.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_22.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_23.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_24.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_25.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_26.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_27.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_28.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_29.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_30.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_31.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_32.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_33.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_34.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_35.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_36.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_37.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_38.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_39.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_40.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_41.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_42.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_43.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_44.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_45.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_46.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_47.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_48.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_49.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_50.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_51.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_52.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_53.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_54.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_55.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_56.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_57.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_58.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_59.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_60.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_61.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_62.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_63.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_64.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_65.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_66.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_67.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (1 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_68.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_69.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_70.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_71.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_72.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_73.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_74.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_75.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_76.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_77.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_78.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_79.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_80.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_81.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_82.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_83.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_84.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_85.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_86.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_87.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_88.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_89.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_90.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_91.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_92.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_93.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_94.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_95.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_96.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_97.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_98.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_99.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_100.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_101.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_102.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_103.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_104.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_105.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_106.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_107.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_108.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_109.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_110.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_111.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_112.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_113.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_114.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_115.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (2 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_116.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_117.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_118.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_119.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_120.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_121.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_122.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_123.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_124.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_125.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_126.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_127.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_128.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_129.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_130.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_131.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_132.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_133.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_134.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_135.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_136.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_137.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_138.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_139.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_140.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_141.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_142.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_143.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_144.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_145.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_146.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_147.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_148.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_149.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_150.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_151.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_152.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_153.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_154.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_155.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_156.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_157.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_158.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_159.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_160.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_161.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_162.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_163.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (3 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_164.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_165.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_166.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_167.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_168.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_169.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_170.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_171.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_172.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_173.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_174.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_175.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_176.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_177.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_178.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_179.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_180.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_181.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_182.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_183.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_184.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_185.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_186.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_187.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_188.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_189.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_190.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_191.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_192.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_193.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_194.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_195.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_196.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_197.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_198.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_199.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_200.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_201.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_202.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_203.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_204.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_205.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_206.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_207.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_208.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_209.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_210.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_211.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_212.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_213.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_214.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_215.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_216.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_217.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_218.symm.trans hj))
  · intro hj
    exact False.elim ((by decide : (4 : Fin 6) ≠ (5 : Fin 6))
      (bulkNearVertex_value_219.symm.trans hj))
  · intro _; exact h220
  · intro _; exact h221
  · intro _; exact h222
  · intro _; exact h223
  · intro _; exact h224
  · intro _; exact h225
  · intro _; exact h226
  · intro _; exact h227
  · intro _; exact h228
  · intro _; exact h229
  · intro _; exact h230
  · intro _; exact h231
  · intro _; exact h232
  · intro _; exact h233


end ProteinFolding.Tetrahedral
