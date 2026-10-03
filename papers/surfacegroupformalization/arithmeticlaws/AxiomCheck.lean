/-
Audit file (not part of the library): run `lake env lean AxiomCheck.lean`.
Expected output for each: [propext, Classical.choice, Quot.sound].
-/
import ArithLaw
open GeodesicArithmetic

#print axioms mobius_inversion
#print axioms s_eq_zero_of_F_eq_zero
#print axioms s_eq_indicator_of_F_eq_inv
#print axioms eq_evendivisors
#print axioms master_of_signlaw
#print axioms solve_divisorsystem
#print axioms primitivelaw_forward
#print axioms primitivelaw_converse
#print axioms unconditional_torus
#print axioms unconditional_surface
#print axioms unconditional_surface_solution
#print axioms signsum_sub_card_even
#print axioms even_card_of_signsum_zero
#print axioms odd_card_of_signsum_one
#print axioms two_le_card_of_signsum_zero
#print axioms abs_signsum_le_card
