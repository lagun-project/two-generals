/**
 * TGP Web Visualizer - Protocol Simulation Module
 *
 * Orchestrates the Two Generals Protocol simulation with:
 * - Configurable packet loss
 * - Speed control
 * - Packet tracking and statistics
 * - Event emission for UI updates
 */

import { ProtocolParty } from './protocol-party.js';
import { createEventEmitter } from './types.js';

export class ProtocolSimulation {
    /**
     * Create a new protocol simulation.
     * @param {number} lossRate - Packet loss rate (0-1)
     */
    constructor(lossRate = 0.5) {
        this.lossRate = lossRate;
        this.alice = new ProtocolParty('Alice', true);
        this.bob = new ProtocolParty('Bob', false);

        // Simulation state
        this.tick = 0;
        this.packetsSent = 0;
        this.packetsLost = 0;
        this.packetsDelivered = 0;
        this.isRunning = false;
        this.speed = 1;

        // In-flight packets
        this.packets = [];

        // Event handling
        const emitter = createEventEmitter();
        this.on = emitter.on;
        this.off = emitter.off;
        this.emit = emitter.emit;

        // Forward party events
        this.alice.on('phaseChange', (data) => {
            this.emit('phaseAdvance', { party: 'alice', phase: data.phase });
        });
        this.bob.on('phaseChange', (data) => {
            this.emit('phaseAdvance', { party: 'bob', phase: data.phase });
        });
    }

    /**
     * Start the protocol simulation.
     */
    start() {
        this.alice.start();
        this.bob.start();
        this.isRunning = true;
        this.emit('start');
    }

    /**
     * Reset the simulation to initial state.
     */
    reset() {
        this.alice.reset();
        this.bob.reset();
        this.tick = 0;
        this.packetsSent = 0;
        this.packetsLost = 0;
        this.packetsDelivered = 0;
        this.isRunning = false;
        this.packets = [];
        this.emit('reset');
    }

    /**
     * Execute one simulation tick.
     * Both parties send their current proof level.
     * Packets in flight are processed.
     */
    step() {
        if (!this.isRunning) return;

        this.tick++;

        // Alice sends to Bob
        const aliceMsg = this.alice.getOutgoingMessage();
        if (aliceMsg) {
            this.sendPacket(aliceMsg, 'alice-to-bob');
        }

        // Bob sends to Alice
        const bobMsg = this.bob.getOutgoingMessage();
        if (bobMsg) {
            this.sendPacket(bobMsg, 'bob-to-alice');
        }

        // Process packets in flight
        this.processPackets();

        // Check for completion
        if (this.alice.isComplete() && this.bob.isComplete()) {
            this.isRunning = false;
            this.emit('complete', {
                outcome: 'ATTACK',
                alice: this.alice,
                bob: this.bob
            });
        }

        this.emit('tick', this.tick);
    }

    /**
     * Send a packet with simulated loss.
     * @param {object} msg - Message to send
     * @param {string} direction - 'alice-to-bob' or 'bob-to-alice'
     */
    sendPacket(msg, direction) {
        this.packetsSent++;
        const isLost = Math.random() < this.lossRate;

        const packet = {
            id: this.packetsSent,
            msg,
            direction,
            progress: 0,
            isLost,
            startTick: this.tick
        };

        this.packets.push(packet);
        this.emit('packetSent', packet);

        if (isLost) {
            this.packetsLost++;
        }
    }

    /**
     * Process packets in flight, advancing their progress.
     */
    processPackets() {
        const arrivedPackets = [];
        const inFlightPackets = [];

        for (const packet of this.packets) {
            packet.progress += 0.2 * this.speed;

            if (packet.progress >= 1) {
                arrivedPackets.push(packet);
            } else {
                inFlightPackets.push(packet);
            }
        }

        this.packets = inFlightPackets;

        // Deliver arrived packets
        for (const packet of arrivedPackets) {
            if (!packet.isLost) {
                this.packetsDelivered++;
                if (packet.direction === 'alice-to-bob') {
                    const advanced = this.bob.receiveMessage(packet.msg);
                    if (advanced) {
                        this.emit('phaseAdvance', { party: 'bob', phase: this.bob.phase });
                    }
                } else {
                    const advanced = this.alice.receiveMessage(packet.msg);
                    if (advanced) {
                        this.emit('phaseAdvance', { party: 'alice', phase: this.alice.phase });
                    }
                }
            }
            this.emit('packetArrived', packet);
        }
    }

    /**
     * Get current simulation statistics.
     * @returns {object} Statistics object
     */
    getStats() {
        return {
            tick: this.tick,
            packetsSent: this.packetsSent,
            packetsLost: this.packetsLost,
            packetsDelivered: this.packetsDelivered,
            actualLossRate: this.packetsSent > 0
                ? (this.packetsLost / this.packetsSent * 100).toFixed(1)
                : 0
        };
    }

    /**
     * Get snapshots of both party states.
     * @returns {object} Party snapshots
     */
    getPartySnapshots() {
        return {
            alice: this.alice.getSnapshot(),
            bob: this.bob.getSnapshot()
        };
    }

    /**
     * Run a complete simulation until completion or deadline.
     * Used for batch testing (Protocol of Theseus).
     *
     * @param {number} maxTicks - Maximum ticks before deadline
     * @returns {object} Simulation result
     */
    runToCompletion(maxTicks = 10000000) {
        this.start();
        let ticks = 0;

        while (ticks < maxTicks && this.isRunning) {
            this.step();
            ticks++;

            // Early termination if both reach QUAD
            if (this.alice.canAttack() && this.bob.canAttack()) {
                return {
                    symmetric: true,
                    aliceDecision: 'ATTACK',
                    bobDecision: 'ATTACK',
                    alicePhase: this.alice.phase,
                    bobPhase: this.bob.phase,
                    ticks,
                    lossRate: this.lossRate,
                    outcome: 'ATTACK',
                    fastForwarded: true
                };
            }
        }

        // Deadline expired
        const aliceDecision = this.alice.getDecision(true);
        const bobDecision = this.bob.getDecision(true);
        const symmetric = aliceDecision === bobDecision;

        return {
            symmetric,
            aliceDecision,
            bobDecision,
            alicePhase: this.alice.phase,
            bobPhase: this.bob.phase,
            ticks,
            lossRate: this.lossRate,
            outcome: symmetric ? aliceDecision : 'ASYMMETRIC',
            fastForwarded: false
        };
    }
}

/**
 * Run a batch of simulations for the Protocol of Theseus test.
 *
 * @param {number[]} lossRates - Array of loss rates to test
 * @param {number} trialsPerRate - Number of trials per loss rate
 * @param {Function} progressCallback - Called after each trial
 * @returns {Promise<object>} Test results
 */
export async function runTheseusTest(lossRates, trialsPerRate, progressCallback) {
    const results = {
        totalTests: lossRates.length * trialsPerRate,
        completed: 0,
        symmetric: 0,
        asymmetric: 0,
        attacks: 0,
        aborts: 0,
        failures: [],
        totalTicks: 0,
        minTicks: Infinity,
        maxTicks: 0
    };

    for (const lossRatePercent of lossRates) {
        const lossRate = lossRatePercent / 100;

        for (let trial = 0; trial < trialsPerRate; trial++) {
            // Run simulation
            const sim = new ProtocolSimulation(lossRate);
            const result = sim.runToCompletion();

            // Update results
            results.completed++;
            results.totalTicks += result.ticks;
            results.minTicks = Math.min(results.minTicks, result.ticks);
            results.maxTicks = Math.max(results.maxTicks, result.ticks);

            if (result.symmetric) {
                results.symmetric++;
                if (result.outcome === 'ATTACK') {
                    results.attacks++;
                } else {
                    results.aborts++;
                }
            } else {
                results.asymmetric++;
                results.failures.push({
                    lossRate: lossRatePercent,
                    trial: trial + 1,
                    result
                });
            }

            // Report progress
            if (progressCallback) {
                await progressCallback({
                    lossRate: lossRatePercent,
                    trial: trial + 1,
                    result,
                    completed: results.completed,
                    total: results.totalTests
                });
            }

            // Yield to event loop periodically
            if (results.completed % 10 === 0) {
                await new Promise(resolve => setTimeout(resolve, 0));
            }
        }
    }

    return results;
}
