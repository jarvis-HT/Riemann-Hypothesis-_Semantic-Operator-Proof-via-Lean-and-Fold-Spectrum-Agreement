import Lake
open Lake DSL

package RiemannHypothesis where
  defaultFacet := PackageFacet.lean

@[default_target]
lean_lib RiemannHypothesis where
  globs := #[.submodules "src"]