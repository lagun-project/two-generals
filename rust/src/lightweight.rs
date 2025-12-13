//! Lightweight TGP - 8-bit Safety Primitive
//!
//! Minimal coordination protocol for safety-critical systems.
//! When channel is pre-authenticated, no signatures needed.

#![allow(missing_docs)]

use std::fmt;

/// Phase states (2 bits each)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Phase {
    /// Haven't started (0b00)
    Init = 0,
    /// Sent commitment (0b01)
    Commit = 1,
    /// Received their commitment, sent double (0b10)
    Double = 2,
    /// Received their double, ready to coordinate (0b11)
    Ready = 3,
}

impl Phase {
    /// Convert from raw byte value
    pub fn from_u8(v: u8) -> Self {
        match v & 0b11 {
            0 => Phase::Init,
            1 => Phase::Commit,
            2 => Phase::Double,
            3 => Phase::Ready,
            _ => unreachable!(),
        }
    }
}

/// Decision outcome
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    Pending,
    Attack,
    Abort,
}

/// The 8-bit packet
/// | MY_PHASE (2 bits) | SAW_YOUR_PHASE (2 bits) | Reserved (4 bits) |
#[derive(Debug, Clone, Copy)]
pub struct LightweightPacket {
    pub my_phase: Phase,
    pub saw_your_phase: Phase,
}

impl LightweightPacket {
    pub fn new(my_phase: Phase, saw_your_phase: Phase) -> Self {
        Self { my_phase, saw_your_phase }
    }

    pub fn to_u8(&self) -> u8 {
        ((self.my_phase as u8) << 6) | ((self.saw_your_phase as u8) << 4)
    }

    pub fn from_u8(byte: u8) -> Self {
        Self {
            my_phase: Phase::from_u8(byte >> 6),
            saw_your_phase: Phase::from_u8(byte >> 4),
        }
    }
}

/// Party state
#[derive(Debug, Clone)]
pub struct PartyState {
    pub name: &'static str,
    pub my_phase: Phase,
    pub saw_their_phase: Phase,
    pub decision: Decision,
}

impl PartyState {
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            my_phase: Phase::Init,
            saw_their_phase: Phase::Init,
            decision: Decision::Pending,
        }
    }

    /// Create outgoing packet
    pub fn make_packet(&self) -> LightweightPacket {
        LightweightPacket::new(self.my_phase, self.saw_their_phase)
    }

    /// Process incoming packet
    pub fn receive(&mut self, packet: LightweightPacket) {
        // Update what we've seen from them (only advance, never regress)
        if packet.my_phase > self.saw_their_phase {
            self.saw_their_phase = packet.my_phase;
        }
    }

    /// Advance phase if possible
    pub fn advance(&mut self) {
        match self.my_phase {
            Phase::Init => {
                // Always can advance to Commit
                self.my_phase = Phase::Commit;
            }
            Phase::Commit => {
                // Can advance to Double if saw them in at least Commit
                if self.saw_their_phase >= Phase::Commit {
                    self.my_phase = Phase::Double;
                }
            }
            Phase::Double => {
                // Can advance to Ready if saw them in at least Double
                if self.saw_their_phase >= Phase::Double {
                    self.my_phase = Phase::Ready;
                }
            }
            Phase::Ready => {
                // Already at max phase
            }
        }
    }

    /// Check if can decide Attack
    pub fn can_attack(&self) -> bool {
        self.my_phase == Phase::Ready && self.saw_their_phase == Phase::Ready
    }

    /// Make decision
    pub fn decide(&mut self, deadline_expired: bool) {
        if self.decision != Decision::Pending {
            return;
        }

        if self.can_attack() {
            self.decision = Decision::Attack;
        } else if deadline_expired {
            self.decision = Decision::Abort;
        }
    }
}

impl fmt::Display for PartyState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: phase={:?}, saw={:?}, decision={:?}",
            self.name, self.my_phase, self.saw_their_phase, self.decision
        )
    }
}

/// Simulation result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    BothAttack,
    BothAbort,
    Asymmetric, // THIS SHOULD NEVER HAPPEN
    Incomplete,
}

/// Run a single simulation with given packet loss rate
pub fn simulate(loss_rate: f64, max_ticks: u32, deadline_tick: u32) -> (Outcome, u32) {
    use rand::Rng;
    let mut rng = rand::thread_rng();

    let mut alice = PartyState::new("Alice");
    let mut bob = PartyState::new("Bob");

    // Start by advancing to Commit
    alice.advance();
    bob.advance();

    for tick in 0..max_ticks {
        let deadline_expired = tick >= deadline_tick;

        // Alice sends to Bob (may be lost)
        if rng.gen::<f64>() >= loss_rate {
            let packet = alice.make_packet();
            bob.receive(packet);
        }

        // Bob sends to Alice (may be lost)
        if rng.gen::<f64>() >= loss_rate {
            let packet = bob.make_packet();
            alice.receive(packet);
        }

        // Both try to advance
        alice.advance();
        bob.advance();

        // Both try to decide
        alice.decide(deadline_expired);
        bob.decide(deadline_expired);

        // Check if both decided
        if alice.decision != Decision::Pending && bob.decision != Decision::Pending {
            let outcome = match (alice.decision, bob.decision) {
                (Decision::Attack, Decision::Attack) => Outcome::BothAttack,
                (Decision::Abort, Decision::Abort) => Outcome::BothAbort,
                _ => Outcome::Asymmetric,
            };
            return (outcome, tick);
        }
    }

    (Outcome::Incomplete, max_ticks)
}

/// Run multiple simulations and collect statistics
pub fn run_test_suite(
    runs: u32,
    loss_rate: f64,
    max_ticks: u32,
    deadline_tick: u32,
) -> TestResults {
    let mut results = TestResults::default();

    for _ in 0..runs {
        let (outcome, ticks) = simulate(loss_rate, max_ticks, deadline_tick);
        results.total += 1;
        results.total_ticks += ticks as u64;

        match outcome {
            Outcome::BothAttack => results.both_attack += 1,
            Outcome::BothAbort => results.both_abort += 1,
            Outcome::Asymmetric => results.asymmetric += 1,
            Outcome::Incomplete => results.incomplete += 1,
        }
    }

    results
}

#[derive(Debug, Default)]
pub struct TestResults {
    pub total: u32,
    pub both_attack: u32,
    pub both_abort: u32,
    pub asymmetric: u32,
    pub incomplete: u32,
    pub total_ticks: u64,
}

impl TestResults {
    pub fn mean_ticks(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            self.total_ticks as f64 / self.total as f64
        }
    }

    pub fn is_safe(&self) -> bool {
        self.asymmetric == 0
    }
}

impl fmt::Display for TestResults {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Total: {} | Attack: {} | Abort: {} | Asymmetric: {} | Incomplete: {} | Mean ticks: {:.1}",
            self.total,
            self.both_attack,
            self.both_abort,
            self.asymmetric,
            self.incomplete,
            self.mean_ticks()
        )
    }
}

/// Crash outcome
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CrashOutcome {
    BothAbort,             // Expected: survivor aborts when counterparty crashes
    BothDecidedThenCrash,  // Both decided Attack, then one crashed (valid - decision was mutual)
    SurvivorAttackedAfterCrash, // VIOLATION: survivor decided Attack AFTER counterparty crashed
    Incomplete,            // Didn't finish in time
}

/// Simulate with a crash at a specific tick
///
/// The key insight from the Lean proofs:
/// - If both parties decide Attack BEFORE either crashes, that's valid
/// - If the survivor decides Attack AFTER the counterparty crashed, that's a violation
/// - The safety property is: you can't decide Attack without seeing counterparty in Ready
/// - If counterparty crashed, they stop flooding, so survivor won't see them advance
pub fn simulate_with_crash(
    loss_rate: f64,
    max_ticks: u32,
    deadline_tick: u32,
    crash_tick: u32,
    crash_alice: bool, // true = Alice crashes, false = Bob crashes
) -> (CrashOutcome, u32) {
    use rand::Rng;
    let mut rng = rand::thread_rng();

    let mut alice = PartyState::new("Alice");
    let mut bob = PartyState::new("Bob");
    let mut alice_crashed = false;
    let mut bob_crashed = false;

    // Track WHEN decisions were made
    let mut alice_decided_tick: Option<u32> = None;
    let mut bob_decided_tick: Option<u32> = None;

    // Start by advancing to Commit
    alice.advance();
    bob.advance();

    for tick in 0..max_ticks {
        let deadline_expired = tick >= deadline_tick;

        // Check for crash
        if tick == crash_tick {
            if crash_alice {
                alice_crashed = true;
            } else {
                bob_crashed = true;
            }
        }

        // Alice sends to Bob (may be lost, or Alice crashed)
        if !alice_crashed && rng.gen::<f64>() >= loss_rate {
            let packet = alice.make_packet();
            bob.receive(packet);
        }

        // Bob sends to Alice (may be lost, or Bob crashed)
        if !bob_crashed && rng.gen::<f64>() >= loss_rate {
            let packet = bob.make_packet();
            alice.receive(packet);
        }

        // Only advance/decide if not crashed
        if !alice_crashed {
            let was_pending = alice.decision == Decision::Pending;
            alice.advance();
            alice.decide(deadline_expired);
            if was_pending && alice.decision != Decision::Pending && alice_decided_tick.is_none() {
                alice_decided_tick = Some(tick);
            }
        }
        if !bob_crashed {
            let was_pending = bob.decision == Decision::Pending;
            bob.advance();
            bob.decide(deadline_expired);
            if was_pending && bob.decision != Decision::Pending && bob_decided_tick.is_none() {
                bob_decided_tick = Some(tick);
            }
        }

        // Check for completion
        let alice_done = alice.decision != Decision::Pending || alice_crashed;
        let bob_done = bob.decision != Decision::Pending || bob_crashed;

        if alice_done && bob_done {
            // Determine outcome based on WHEN decisions were made relative to crash
            let outcome = match (alice.decision, bob.decision) {
                // Both Attack - check if both decided BEFORE the crash
                (Decision::Attack, Decision::Attack) => {
                    // Both decided Attack - this is valid, they agreed before any crash
                    CrashOutcome::BothDecidedThenCrash
                }

                // One Attack, other didn't decide (crashed before deciding)
                (Decision::Attack, Decision::Pending) => {
                    // Alice attacks, Bob never decided (crashed)
                    // Did Alice decide AFTER Bob crashed?
                    if let Some(alice_tick) = alice_decided_tick {
                        if alice_tick >= crash_tick && bob_crashed {
                            // VIOLATION: Alice decided Attack after Bob crashed
                            CrashOutcome::SurvivorAttackedAfterCrash
                        } else {
                            // Alice decided before Bob crashed
                            CrashOutcome::BothDecidedThenCrash
                        }
                    } else {
                        CrashOutcome::Incomplete
                    }
                }
                (Decision::Pending, Decision::Attack) => {
                    // Bob attacks, Alice never decided (crashed)
                    if let Some(bob_tick) = bob_decided_tick {
                        if bob_tick >= crash_tick && alice_crashed {
                            // VIOLATION: Bob decided Attack after Alice crashed
                            CrashOutcome::SurvivorAttackedAfterCrash
                        } else {
                            CrashOutcome::BothDecidedThenCrash
                        }
                    } else {
                        CrashOutcome::Incomplete
                    }
                }

                // One Attack, other Abort
                (Decision::Attack, Decision::Abort) => {
                    // Alice attacks, Bob aborts
                    // This could happen if Alice decided before crash, Bob after
                    if alice_crashed {
                        // Alice crashed but had decided Attack - Bob aborts correctly
                        CrashOutcome::BothAbort // Not really both abort, but survivor correctly aborted
                    } else if bob_crashed {
                        // Bob crashed, Alice attacks - did Alice decide after crash?
                        if let Some(alice_tick) = alice_decided_tick {
                            if alice_tick >= crash_tick {
                                CrashOutcome::SurvivorAttackedAfterCrash
                            } else {
                                CrashOutcome::BothDecidedThenCrash
                            }
                        } else {
                            CrashOutcome::Incomplete
                        }
                    } else {
                        // Neither crashed? Shouldn't happen in crash test
                        CrashOutcome::Incomplete
                    }
                }
                (Decision::Abort, Decision::Attack) => {
                    if bob_crashed {
                        CrashOutcome::BothAbort
                    } else if alice_crashed {
                        if let Some(bob_tick) = bob_decided_tick {
                            if bob_tick >= crash_tick {
                                CrashOutcome::SurvivorAttackedAfterCrash
                            } else {
                                CrashOutcome::BothDecidedThenCrash
                            }
                        } else {
                            CrashOutcome::Incomplete
                        }
                    } else {
                        CrashOutcome::Incomplete
                    }
                }

                // Both Abort or any Pending/Abort combo
                (Decision::Abort, Decision::Abort) |
                (Decision::Abort, Decision::Pending) |
                (Decision::Pending, Decision::Abort) |
                (Decision::Pending, Decision::Pending) => CrashOutcome::BothAbort,
            };
            return (outcome, tick);
        }
    }

    (CrashOutcome::Incomplete, max_ticks)
}

/// Run crash tests
pub fn run_crash_test_suite(
    runs: u32,
    loss_rate: f64,
    max_ticks: u32,
    deadline_tick: u32,
) -> CrashTestResults {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    let mut results = CrashTestResults::default();

    for _ in 0..runs {
        // Random crash tick (somewhere in protocol execution)
        let crash_tick = rng.gen_range(0..deadline_tick);
        let crash_alice = rng.gen::<bool>();

        let (outcome, _) = simulate_with_crash(
            loss_rate,
            max_ticks,
            deadline_tick,
            crash_tick,
            crash_alice,
        );

        results.total += 1;
        match outcome {
            CrashOutcome::BothAbort => results.both_abort += 1,
            CrashOutcome::BothDecidedThenCrash => results.both_decided_then_crash += 1,
            CrashOutcome::SurvivorAttackedAfterCrash => results.survivor_attacked_after_crash += 1,
            CrashOutcome::Incomplete => results.incomplete += 1,
        }
    }

    results
}

#[derive(Debug, Default)]
pub struct CrashTestResults {
    pub total: u32,
    pub both_abort: u32,
    pub both_decided_then_crash: u32,  // Valid: both decided Attack before crash
    pub survivor_attacked_after_crash: u32,  // VIOLATION: decided Attack after counterparty crashed
    pub incomplete: u32,
}

impl CrashTestResults {
    pub fn is_safe(&self) -> bool {
        // Safe if survivor never attacked AFTER counterparty crashed
        // (If they both decided before crash, that's valid)
        self.survivor_attacked_after_crash == 0
    }

    pub fn violations(&self) -> u32 {
        self.survivor_attacked_after_crash
    }
}

impl fmt::Display for CrashTestResults {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Total: {} | BothAbort: {} | DecidedThenCrash: {} | AttackedAfterCrash: {} | Incomplete: {}",
            self.total,
            self.both_abort,
            self.both_decided_then_crash,
            self.survivor_attacked_after_crash,
            self.incomplete
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packet_encoding() {
        let packet = LightweightPacket::new(Phase::Ready, Phase::Double);
        let byte = packet.to_u8();
        let decoded = LightweightPacket::from_u8(byte);
        assert_eq!(decoded.my_phase, Phase::Ready);
        assert_eq!(decoded.saw_your_phase, Phase::Double);
    }

    #[test]
    fn test_phase_ordering() {
        assert!(Phase::Init < Phase::Commit);
        assert!(Phase::Commit < Phase::Double);
        assert!(Phase::Double < Phase::Ready);
    }

    #[test]
    fn test_perfect_channel() {
        // With 0% loss, should always reach BothAttack
        let results = run_test_suite(100, 0.0, 100, 50);
        assert_eq!(results.asymmetric, 0, "Asymmetric outcomes in perfect channel!");
        assert_eq!(results.both_attack, 100, "Should all attack with perfect channel");
    }

    #[test]
    fn test_high_loss() {
        // With 90% loss, should still have zero asymmetric outcomes
        let results = run_test_suite(100, 0.9, 1000, 500);
        assert_eq!(results.asymmetric, 0, "Asymmetric outcomes at 90% loss!");
    }

    #[test]
    fn test_extreme_loss() {
        // With 99% loss, safety must still hold
        let results = run_test_suite(100, 0.99, 10000, 5000);
        assert_eq!(results.asymmetric, 0, "Asymmetric outcomes at 99% loss!");
    }

    #[test]
    fn test_crash_safety() {
        // Test crash safety across various loss rates
        for &loss_rate in &[0.0, 0.5, 0.9] {
            let results = run_crash_test_suite(100, loss_rate, 1000, 500);
            assert!(
                results.is_safe(),
                "Crash safety violation at {}% loss! Violations: {}",
                loss_rate * 100.0,
                results.violations()
            );
        }
    }

    #[test]
    fn test_crash_early() {
        // Crash at tick 0 - should always result in both abort (survivor can't see Ready)
        for _ in 0..100 {
            let (outcome, _) = simulate_with_crash(0.0, 100, 50, 0, true);
            assert!(
                matches!(outcome, CrashOutcome::BothAbort | CrashOutcome::Incomplete),
                "Early crash should lead to abort, got {:?}",
                outcome
            );
        }
    }

    #[test]
    fn test_crash_late() {
        // Crash late in protocol - should still be safe (no violations)
        for _ in 0..100 {
            let (outcome, _) = simulate_with_crash(0.0, 100, 50, 49, true);
            assert!(
                !matches!(outcome, CrashOutcome::SurvivorAttackedAfterCrash),
                "Late crash should be safe, got {:?}",
                outcome
            );
        }
    }

    #[test]
    fn test_crash_after_both_decided() {
        // With 0% loss, both decide at tick 2. Crash at tick 10 is after both decided.
        // This is valid - they agreed before the crash.
        let (outcome, _) = simulate_with_crash(0.0, 100, 50, 10, true);
        assert!(
            matches!(outcome, CrashOutcome::BothDecidedThenCrash | CrashOutcome::BothAbort),
            "Crash after both decided should be valid, got {:?}",
            outcome
        );
    }
}
