(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "~/AgdaSandbox/.cabal-sandbox/bin/agda-mode locate")))
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(agda-input-user-translations (quote (("abc+" "∀ {α β γ} {A : ★ α} {B : ★ β} {C : ★ γ}") ("abcd+" "∀ {α β γ δ} {A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ d}") ("ab+" "∀ {α β} {A : ★ α} {B : ★ β}") ("abcd3" "{ α } { β } { γ } { δ } { A } { B } { C } { D }") ("abg3" "{ α } { β } { γ } { A } { B } { C }") ("abc3" "{ α } { β } { γ } { A } { B } { C }") ("ab3" "{ α } { β } { A } { B }") ("ABCD2" "{A} {B} {C} {D}") ("ABC2" "{A} {B} {C}") ("AB2" "{A} {B}") ("ABCD" "{A : ★ α} {B : ★ β} {C : ★ γ} {D : ★ d}") ("ABC" "{A : ★ α} {B : ★ β} {C : ★ γ}") ("AB" "{A : ★ α} {B : ★ β}") ("abg2" "{α} {β} {γ}") ("abg" "{α β γ}") ("abcd2" "{α} {β} {γ} {δ}") ("abc2" "{α} {β} {γ}") ("ab2" "{α} {β}") ("abcd" "{α β γ δ}") ("abc" "{α β γ}") ("ab" "{α β}") ("nuke" "☢") ("p3" "π₃") ("elim" "▷") ("cons" "◁") ("off" "◯") ("on" "●") ("iso" "≅") ("w" "ω") ("bi" "⇆") ("inv" "⁻¹") ("p2" "π₂") ("p1" "π₁") ("neq" "≢") ("eq" "≡") ("id" "≡") ("r" "→") ("trans" "⇶") ("sym" "↑↓") ("refl" "⟲") ("s" "𝕤") ("z" "𝕫") ("f" "𝕗") ("t" "𝕥") ("Z" "ℤ") ("R" "ℝ") ("Q" "ℚ") ("N" "ℕ") ("C" "ℂ") ("B" "𝔹") ("G" "Γ") ("D" "Δ") ("l" "λ") ("T" "⊤") ("E" "∃") ("A" "∀") ("S" "Σ") ("P" "Π") ("F" "⊥") ("max" "⊔") ("set1" "★₁") ("set0" "★₀") ("set" "★") ("d" "δ") ("g" "γ") ("b" "β") ("a" "α")))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
