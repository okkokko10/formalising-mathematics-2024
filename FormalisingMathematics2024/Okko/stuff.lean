import Mathlib.tactic



-- theorem matrix_dot_exchange
--   {A B F iA iB iF C : Type}
--   {a : iA → A} {b : iB → B}
--   [Fintype iA] [Fintype iB] [Fintype iF]
--   {Hfb : (iF → F) → (iB → B) → C }
--   {Haf : (iA → A) → (iFt → Ft) → C }
--   {f : (iA → A) → (iF → F) }
--   {}
--   :


theorem matrix_dot_exchange
  {A B C : Type}
  {X Y : Type}
  {sX : Finset X}
  {sY : Finset Y}
  {a : Y → A} {b : X → B}
  [Fintype Y] [Fintype X]
  [AddCommMonoid (X → B)]
  [AddCommMonoid C]
  {H : B → B → C }
  [HAdd B B B]
  {Ht : A → A → C }
  {F  : (Y → A) → (X → B) }
  {Ft : (X → B) → (Y → A) }
  (H_ldistr : ∀(x y z), H (x + y) z = H x z + H y z)
  (H_rdistr : ∀(x y z), H x (y + z) = H x y + H x z)
  :
    Finset.sum sX (fun x ↦ H (F a x) (b x)) =
    Finset.sum sY (fun y ↦ Ht (a y) (Ft b y))

    :=
    by
      sorry
