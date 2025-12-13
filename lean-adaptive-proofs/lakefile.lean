/-
  Lakefile for Adaptive Flooding Proofs

  Integrates the adaptive flooding formal proofs into the build system.
-/

import Lake
open Lake DSL

package «adaptive-flooding-proofs» {
  -- Add package configuration options here
}

-- Depend on the main two-generals-proof package
require «two-generals-proof» from "../lean4"

-- Adaptive flooding proofs libraries
@[default_target]
lean_lib «AdaptiveBilateral» {
  -- Bilateral preservation theorem
  -- Proves adaptive rate modulation preserves bilateral construction
}

lean_lib «Convergence» {
  -- Convergence theorem
  -- Proves protocol converges under fair channel
}

lean_lib «RateSafety» {
  -- Rate modulation safety
  -- Proves rate stays within bounds
}
