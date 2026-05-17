import Lake
open Lake DSL

package «CertifyEdge» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «CertifyEdge» where
  roots := #[`CertifyEdge]
