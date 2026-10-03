/-
Audit file (not part of the library): run `lake env lean AxiomCheck.lean`.
Expected output for each: [propext, Classical.choice, Quot.sound].
-/
import Potency

#print axioms Potency.potentAt_of_residuallyFree
#print axioms Potency.potentAt_freeGroup
#print axioms Potency.freeGroup_exists_orderOf_eq
#print axioms Potency.exists_coeff_ne_zero
#print axioms Potency.exists_addOrderOf_eq_prime
