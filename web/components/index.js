/**
 * TGP Web Visualizer - Components Index
 *
 * Barrel export for all visualization components.
 * Import from this file for clean, organized imports:
 *
 * import { PacketVisualizer, ProtocolSimulation, Phase } from './components/index.js';
 */

// =============================================================================
// Shared Types and Utilities
// =============================================================================
export {
    Phase,
    phaseName,
    phaseDescription,
    Decision,
    Colors,
    Timing,
    generateSignature,
    generateHash,
    formatNumber,
    formatPercent,
    createEventEmitter,
    debounce,
    throttle
} from './types.js';

// =============================================================================
// Protocol Logic Components
// =============================================================================
export { ProtocolParty } from './protocol-party.js';
export {
    ProtocolSimulation,
    runTheseusTest
} from './protocol-simulation.js';

// =============================================================================
// Visualization Components
// =============================================================================
export {
    PacketVisualizer,
    createPacketVisualizerWithControls
} from './packet-visualizer.js';

export {
    BattlefieldScene,
    createBattlefieldDemo
} from './battlefield.js';

export {
    InfiniteRegressVisualizer,
    createInfiniteRegressDemo
} from './infinite-regress.js';

export {
    ProofMergingVisualizer,
    createProofMergingDemo
} from './proof-merging.js';

// =============================================================================
// Component Factory - Create all components for a container
// =============================================================================

/**
 * Initialize all visualization components.
 * @param {object} containers - Object mapping component names to container IDs
 * @returns {object} Object with all initialized component instances
 */
export function initializeComponents(containers = {}) {
    const components = {};

    if (containers.battlefield) {
        const { createBattlefieldDemo } = require('./battlefield.js');
        components.battlefield = createBattlefieldDemo(containers.battlefield);
    }

    if (containers.infiniteRegress) {
        const { createInfiniteRegressDemo } = require('./infinite-regress.js');
        components.infiniteRegress = createInfiniteRegressDemo(containers.infiniteRegress);
    }

    if (containers.proofMerging) {
        const { createProofMergingDemo } = require('./proof-merging.js');
        components.proofMerging = createProofMergingDemo(containers.proofMerging);
    }

    if (containers.packets) {
        const { createPacketVisualizerWithControls } = require('./packet-visualizer.js');
        components.packets = createPacketVisualizerWithControls(containers.packets);
    }

    return components;
}
