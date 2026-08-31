/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
import MoebiusTranscendental.Basic
import MoebiusTranscendental.Multiplicity
import MoebiusTranscendental.Spectrum

/-!
# Axiom verification

Permanent axiom checks, printed by `lake build`. The expected output is that
every declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`, and that several depend on strictly fewer.

These are `#print axioms` commands rather than tests: they cannot fail the
build, but they put the assumed surface in the build log where a regression is
visible rather than silent.
-/

namespace MoebiusTranscendental

#print axioms Qbar
#print axioms mem_Qbar_iff
#print axioms Transcendentals
#print axioms gen
#print axioms conjDegree
#print axioms stratum
#print axioms shiftTo
#print axioms mult
#print axioms nonempty_of_ne_zero
#print axioms shiftTo_ne_zero

-- Spectrum
#print axioms conjDegree_ne_zero
#print axioms finiteWitness_degree
#print axioms finite_spectrum
#print axioms top_witness_exists
#print axioms spectrum_statement_compiles
#print axioms stratum_nonempty
#print axioms stratum_zero

end MoebiusTranscendental
