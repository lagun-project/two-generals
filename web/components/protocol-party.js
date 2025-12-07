/**
 * TGP Web Visualizer - Protocol Party Module
 *
 * Represents one party (general) in the Two Generals Protocol.
 * Implements the proof escalation ladder: C -> D -> T -> Q
 *
 * Key Protocol Properties:
 * 1. Each proof level embeds the previous (self-certifying)
 * 2. Receiving a higher proof extracts all lower proofs
 * 3. Bilateral construction: Q_A exists iff Q_B is constructible
 */

import { Phase, generateSignature, generateHash, createEventEmitter } from './types.js';

export class ProtocolParty {
    /**
     * Create a protocol party.
     * @param {string} name - Party name ('Alice' or 'Bob')
     * @param {boolean} isAlice - True if this is Alice's side
     */
    constructor(name, isAlice) {
        this.name = name;
        this.isAlice = isAlice;
        this.phase = Phase.INIT;

        // Own proofs constructed at each level
        this.commitment = null;      // C_X: Signed commitment
        this.doubleProof = null;     // D_X: Contains C_X + C_Y
        this.tripleProof = null;     // T_X: Contains D_X + D_Y
        this.quadProof = null;       // Q_X: Contains T_X + T_Y

        // Counterparty proofs received
        this.otherCommitment = null;
        this.otherDoubleProof = null;
        this.otherTripleProof = null;

        // Message queue for pending deliveries
        this.messageQueue = [];

        // Proof artifacts for UI visualization
        this.proofArtifacts = [];

        // Track embedded proofs for debugging
        this.embeddedProofs = new Set();

        // Event emitter for state changes
        const emitter = createEventEmitter();
        this.on = emitter.on;
        this.off = emitter.off;
        this.emit = emitter.emit;
    }

    /**
     * Start the protocol by generating initial commitment.
     */
    start() {
        if (this.phase === Phase.INIT) {
            this.commitment = this.createCommitment();
            this.phase = Phase.COMMITMENT;
            this.proofArtifacts.push({
                type: 'commitment',
                label: `C_${this.isAlice ? 'A' : 'B'}`,
                description: 'Signed commitment to attack'
            });
            this.emit('phaseChange', { phase: this.phase, party: this.name });
        }
    }

    /**
     * Create a signed commitment.
     * @returns {object} Commitment proof
     */
    createCommitment() {
        return {
            party: this.name,
            message: 'I will attack at dawn if you agree',
            signature: generateSignature(),
            hash: generateHash()
        };
    }

    /**
     * Get the current outgoing message based on phase.
     * @returns {object|null} Message to send or null
     */
    getOutgoingMessage() {
        switch (this.phase) {
            case Phase.COMMITMENT:
                return { type: 'C', proof: this.commitment };
            case Phase.DOUBLE:
                return { type: 'D', proof: this.doubleProof };
            case Phase.TRIPLE:
                return { type: 'T', proof: this.tripleProof };
            case Phase.QUAD:
                return { type: 'Q', proof: this.quadProof };
            default:
                return null;
        }
    }

    /**
     * Receive and process a message with PROPER PROOF EMBEDDING.
     *
     * CRITICAL PROTOCOL FEATURE: Higher proofs embed all lower proofs!
     * - D contains: C_A, C_B
     * - T contains: D_A, D_B (which contain C_A, C_B)
     * - Q contains: T_A, T_B (which contain everything)
     *
     * This means: If I receive T_Y, I can extract C_Y and D_Y from it!
     *
     * @param {object} msg - Message with type and proof
     * @returns {boolean} True if phase advanced
     */
    receiveMessage(msg) {
        if (!msg) return false;

        let advanced = false;

        // PROOF EMBEDDING: Extract all embedded proofs from higher-level messages
        if (msg.type === 'Q' && msg.proof) {
            if (msg.proof.otherTriple) {
                this.processEmbeddedTriple(msg.proof.otherTriple);
            }
            if (msg.proof.ownTriple) {
                this.processEmbeddedTriple(msg.proof.ownTriple);
            }
        }

        if (msg.type === 'T' && msg.proof) {
            this.processEmbeddedTriple(msg.proof);
        }

        if (msg.type === 'D' && msg.proof) {
            this.processEmbeddedDouble(msg.proof);
        }

        // After extracting embedded proofs, try to advance through phases
        advanced = this.tryAdvanceToQuad() || advanced;

        // Now process the message itself
        switch (msg.type) {
            case 'C':
                if (!this.otherCommitment) {
                    this.otherCommitment = msg.proof;
                    this.tryAdvanceToDouble();
                    advanced = true;
                }
                break;

            case 'D':
                if (!this.otherDoubleProof && msg.proof) {
                    this.otherDoubleProof = msg.proof;
                    this.tryAdvanceToTriple();
                    advanced = true;
                }
                break;

            case 'T':
                if (!this.otherTripleProof && msg.proof) {
                    this.otherTripleProof = msg.proof;
                    this.embeddedProofs.add('T_other');
                    this.tryAdvanceToQuad();
                    advanced = true;
                }
                break;

            case 'Q':
                if (this.phase === Phase.QUAD) {
                    this.phase = Phase.COMPLETE;
                    this.emit('phaseChange', { phase: this.phase, party: this.name });
                    advanced = true;
                }
                break;
        }

        return advanced;
    }

    /**
     * Extract embedded proofs from a Triple proof.
     * T contains D_X and D_Y, each of which contains C_X and C_Y.
     *
     * CRITICAL: Must check party field before setting "other" proofs!
     * @param {object} triple - Triple proof to extract from
     */
    processEmbeddedTriple(triple) {
        if (!triple) return;

        // Extract embedded doubles
        if (triple.ownDouble) {
            this.processEmbeddedDouble(triple.ownDouble);
            if (!this.otherDoubleProof && triple.ownDouble.party !== this.name) {
                this.otherDoubleProof = triple.ownDouble;
                this.embeddedProofs.add('D_other_from_T_own');
            }
        }
        if (triple.otherDouble) {
            this.processEmbeddedDouble(triple.otherDouble);
            if (!this.otherDoubleProof && triple.otherDouble.party !== this.name) {
                this.otherDoubleProof = triple.otherDouble;
                this.embeddedProofs.add('D_other_from_T_other');
            }
        }

        // If this is the other party's triple, we can use it directly
        if (triple.party !== this.name && !this.otherTripleProof) {
            this.otherTripleProof = triple;
            this.embeddedProofs.add('T_other_embedded');
        }
    }

    /**
     * Extract embedded proofs from a Double proof.
     * D contains C_X and C_Y.
     * @param {object} double - Double proof to extract from
     */
    processEmbeddedDouble(double) {
        if (!double) return;

        if (double.otherCommitment && !this.otherCommitment) {
            if (double.otherCommitment.party !== this.name) {
                this.otherCommitment = double.otherCommitment;
                this.embeddedProofs.add('C_other_from_D');
            }
        }
        if (double.ownCommitment && double.ownCommitment.party !== this.name) {
            if (!this.otherCommitment) {
                this.otherCommitment = double.ownCommitment;
                this.embeddedProofs.add('C_other_from_D');
            }
        }
    }

    /**
     * Try to advance to Double phase if requirements met.
     * @returns {boolean} True if advanced
     */
    tryAdvanceToDouble() {
        if (this.phase === Phase.COMMITMENT && this.otherCommitment && !this.doubleProof) {
            this.doubleProof = this.createDoubleProof();
            this.phase = Phase.DOUBLE;
            this.proofArtifacts.push({
                type: 'double',
                label: `D_${this.isAlice ? 'A' : 'B'}`,
                description: 'Contains both commitments'
            });
            this.emit('phaseChange', { phase: this.phase, party: this.name });
            return true;
        }
        return false;
    }

    /**
     * Try to advance to Triple phase if requirements met.
     * @returns {boolean} True if advanced
     */
    tryAdvanceToTriple() {
        let didAdvance = false;

        // Ensure we're caught up from Commitment to Double
        if (this.phase === Phase.COMMITMENT && this.otherCommitment) {
            didAdvance = this.tryAdvanceToDouble() || didAdvance;
        }

        // Now try to advance to Triple
        if (this.phase === Phase.DOUBLE && this.otherDoubleProof && !this.tripleProof) {
            this.tripleProof = this.createTripleProof();
            this.phase = Phase.TRIPLE;
            this.proofArtifacts.push({
                type: 'triple',
                label: `T_${this.isAlice ? 'A' : 'B'}`,
                description: 'Contains both double proofs'
            });
            this.emit('phaseChange', { phase: this.phase, party: this.name });
            didAdvance = true;
        }
        return didAdvance;
    }

    /**
     * Try to advance to Quad phase if requirements met.
     * @returns {boolean} True if advanced
     */
    tryAdvanceToQuad() {
        let didAdvance = false;

        // Ensure we're caught up on previous phases
        didAdvance = this.tryAdvanceToTriple() || didAdvance;

        if (this.phase === Phase.TRIPLE && this.otherTripleProof && !this.quadProof) {
            this.quadProof = this.createQuadProof();
            this.phase = Phase.QUAD;
            this.proofArtifacts.push({
                type: 'quad',
                label: `Q_${this.isAlice ? 'A' : 'B'}`,
                description: 'Epistemic fixpoint achieved! (Q proves mutual constructibility)'
            });
            this.emit('phaseChange', { phase: this.phase, party: this.name });
            didAdvance = true;
        }
        return didAdvance;
    }

    /**
     * Create a Double proof embedding both commitments.
     * @returns {object} Double proof
     */
    createDoubleProof() {
        return {
            party: this.name,
            ownCommitment: this.commitment,
            otherCommitment: this.otherCommitment,
            signature: generateSignature(),
            hash: generateHash()
        };
    }

    /**
     * Create a Triple proof embedding both double proofs.
     * @returns {object} Triple proof
     */
    createTripleProof() {
        return {
            party: this.name,
            ownDouble: this.doubleProof,
            otherDouble: this.otherDoubleProof,
            signature: generateSignature(),
            hash: generateHash()
        };
    }

    /**
     * Create a Quad proof embedding both triple proofs.
     * @returns {object} Quad proof (epistemic fixpoint)
     */
    createQuadProof() {
        return {
            party: this.name,
            ownTriple: this.tripleProof,
            otherTriple: this.otherTripleProof,
            signature: generateSignature(),
            hash: generateHash()
        };
    }

    /**
     * Check if protocol is complete.
     * @returns {boolean} True if complete
     */
    isComplete() {
        return this.phase === Phase.COMPLETE;
    }

    /**
     * Check if party can decide to attack.
     * Party decides ATTACK upon constructing Q (Phase.QUAD).
     * @returns {boolean} True if can attack
     */
    canAttack() {
        return this.phase >= Phase.QUAD;
    }

    /**
     * Get the final decision based on protocol state.
     *
     * PROTOCOL RULES:
     * - Upon constructing Q_X: decide ATTACK
     * - Upon deadline expires without Q: decide ABORT
     *
     * @param {boolean} deadlineExpired - Whether deadline has passed
     * @returns {string} 'ATTACK', 'ABORT', or 'PENDING'
     */
    getDecision(deadlineExpired) {
        if (this.phase >= Phase.QUAD) {
            return 'ATTACK';
        }
        if (deadlineExpired) {
            return 'ABORT';
        }
        return 'PENDING';
    }

    /**
     * Reset the party to initial state.
     */
    reset() {
        this.phase = Phase.INIT;
        this.commitment = null;
        this.doubleProof = null;
        this.tripleProof = null;
        this.quadProof = null;
        this.otherCommitment = null;
        this.otherDoubleProof = null;
        this.otherTripleProof = null;
        this.messageQueue = [];
        this.proofArtifacts = [];
        this.embeddedProofs.clear();
    }

    /**
     * Get a serializable snapshot of the party state.
     * @returns {object} State snapshot
     */
    getSnapshot() {
        return {
            name: this.name,
            isAlice: this.isAlice,
            phase: this.phase,
            hasCommitment: !!this.commitment,
            hasDoubleProof: !!this.doubleProof,
            hasTripleProof: !!this.tripleProof,
            hasQuadProof: !!this.quadProof,
            hasOtherCommitment: !!this.otherCommitment,
            hasOtherDoubleProof: !!this.otherDoubleProof,
            hasOtherTripleProof: !!this.otherTripleProof,
            proofArtifacts: [...this.proofArtifacts],
            embeddedProofs: [...this.embeddedProofs]
        };
    }
}
