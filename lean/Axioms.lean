import Garden.M3Codes
/-! `lake env lean Axioms.lean` prints the main theorems' statements and the axioms each depends on.
reproduce.sh requires every list to be within `propext`, `Classical.choice`, `Quot.sound` (a `sorry`
would show up as `sorryAx`, `native_decide` as `Lean.ofReduceBool`). -/
#check @M3Codes.m3v4g11_all
#print axioms M3Codes.m3v4g11_all
#print axioms M3Codes.m3v4g11_all_direct
#print axioms M3Codes.validCode_iff
#print axioms M3Codes.codes60_length
#print axioms M3Codes.classify
#print axioms M3Codes.computes_swap
#print axioms M3Codes.computes_neg0
#print axioms M3Codes.computes_shift
#print axioms M3Codes.jobs_cover
#print axioms M3Jobs.jobs_length
#print axioms M3Reduce.m3v4g11
#print axioms M3Sound.m3v4g11_le11
#print axioms Garden.M3Direct.sound
#print axioms Garden.LratDirect.check_sound
