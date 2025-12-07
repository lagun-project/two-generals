import Lake
open Lake DSL

package «two-generals-proof» {
  -- add package configuration options here
}

-- NOTE: Proofs are self-contained with axioms for Real, Time, etc.
-- No Mathlib dependency required.

@[default_target]
lean_lib «TwoGenerals» {
  -- add library configuration options here
}

lean_lib «NetworkModel» {
  -- Layer 2: Probabilistic network reliability
}

lean_lib «TimeoutMechanism» {
  -- Layer 3: Timeout-based coordinated abort
}

lean_lib «MainTheorem» {
  -- Layer 4: Complete integration
}

lean_lib «ExtremeLoss» {
  -- Layer 5: Extreme loss scenario (99.9999% loss, 1000 msg/sec, 18 hours)
}
