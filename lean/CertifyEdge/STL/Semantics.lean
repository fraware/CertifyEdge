/-!
Signal-time STL fragment (simulation profile): formulas as `Float → Prop`.
-/

namespace CertifyEdge.STL

abbrev Time := Float

def inInterval (t lo hi : Time) : Prop :=
  lo ≤ t ∧ t ≤ hi

def stl_always (lo hi : Time) (φ : Time → Prop) : Prop :=
  ∀ t, inInterval t lo hi → φ t

def stl_eventually (lo hi : Time) (φ : Time → Prop) : Prop :=
  ∃ t, inInterval t lo hi ∧ φ t

end CertifyEdge.STL
