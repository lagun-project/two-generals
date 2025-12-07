/**
 * TGP Web Visualizer - Shared Types and Constants
 *
 * This module provides shared types, constants, and utility functions
 * used across all visualization components.
 */

// =============================================================================
// Protocol Phase Types
// =============================================================================

/**
 * Protocol phases representing the proof escalation ladder.
 * Each phase embeds proofs from previous phases.
 */
export const Phase = {
    INIT: 0,        // Not started
    COMMITMENT: 1,  // C: Signed commitment to attack
    DOUBLE: 2,      // D: Contains both C_A and C_B
    TRIPLE: 3,      // T: Contains both D_A and D_B
    QUAD: 4,        // Q: Contains both T_A and T_B (epistemic fixpoint)
    COMPLETE: 5     // Protocol completed successfully
};

/**
 * Get human-readable phase name.
 * @param {number} phase - Phase value from Phase enum
 * @returns {string} Phase name
 */
export function phaseName(phase) {
    switch (phase) {
        case Phase.INIT: return 'INIT';
        case Phase.COMMITMENT: return 'C';
        case Phase.DOUBLE: return 'D';
        case Phase.TRIPLE: return 'T';
        case Phase.QUAD: return 'Q';
        case Phase.COMPLETE: return 'COMPLETE';
        default: return 'UNKNOWN';
    }
}

/**
 * Get full phase description.
 * @param {number} phase - Phase value
 * @returns {string} Full description
 */
export function phaseDescription(phase) {
    switch (phase) {
        case Phase.INIT: return 'Initialization';
        case Phase.COMMITMENT: return 'Commitment (C) - Signed intent to attack';
        case Phase.DOUBLE: return 'Double Proof (D) - Both parties committed';
        case Phase.TRIPLE: return 'Triple Proof (T) - Both have double proofs';
        case Phase.QUAD: return 'Quad Proof (Q) - Epistemic fixpoint achieved';
        case Phase.COMPLETE: return 'Protocol Complete';
        default: return 'Unknown Phase';
    }
}

// =============================================================================
// Decision Types
// =============================================================================

export const Decision = {
    PENDING: 'PENDING',
    ATTACK: 'ATTACK',
    ABORT: 'ABORT'
};

// =============================================================================
// Color Palette
// =============================================================================

/**
 * Consistent color palette used across all visualizations.
 * Based on GitHub's dark theme for readability.
 */
export const Colors = {
    // Party colors
    alice: '#58a6ff',      // Blue for Alice
    bob: '#3fb950',        // Green for Bob

    // Proof level colors
    commitment: '#d29922',  // Yellow/gold for C
    double: '#a371f7',      // Purple for D
    triple: '#f0883e',      // Orange for T
    quad: '#56d364',        // Bright green for Q

    // UI colors
    text: '#f0f6fc',        // Primary text
    muted: '#8b949e',       // Secondary text
    bg: '#21262d',          // Background
    bgDark: '#161b22',      // Darker background
    border: '#30363d',      // Border color

    // State colors
    success: '#3fb950',
    error: '#f85149',
    warning: '#d29922',
    info: '#58a6ff'
};

// =============================================================================
// Animation Timing
// =============================================================================

export const Timing = {
    fast: 150,          // Fast transitions
    normal: 300,        // Standard transitions
    slow: 500,          // Slower, more noticeable
    packet: 100,        // Packet animation tick
    proof: 400          // Proof construction animation
};

// =============================================================================
// Utility Functions
// =============================================================================

/**
 * Generate a random hex signature (simulated).
 * @param {number} length - Number of hex characters
 * @returns {string} Random hex string
 */
export function generateSignature(length = 8) {
    return Array.from({ length }, () =>
        Math.floor(Math.random() * 16).toString(16)
    ).join('');
}

/**
 * Generate a random hash (simulated).
 * @param {number} length - Number of hex characters
 * @returns {string} Random hex string
 */
export function generateHash(length = 16) {
    return generateSignature(length);
}

/**
 * Format a number with appropriate suffix (k, M, B).
 * @param {number} n - Number to format
 * @returns {string} Formatted string
 */
export function formatNumber(n) {
    if (n >= 1e9) return (n / 1e9).toFixed(1) + 'B';
    if (n >= 1e6) return (n / 1e6).toFixed(1) + 'M';
    if (n >= 1e3) return (n / 1e3).toFixed(1) + 'k';
    return n.toString();
}

/**
 * Format a percentage with appropriate precision.
 * @param {number} value - Value between 0 and 1
 * @param {number} minDecimals - Minimum decimal places
 * @returns {string} Formatted percentage string
 */
export function formatPercent(value, minDecimals = 1) {
    const percent = value * 100;
    if (percent >= 99.9) {
        // Show more precision for high percentages
        const precision = Math.max(minDecimals, Math.ceil(Math.log10(1 / (100 - percent))));
        return percent.toFixed(precision) + '%';
    }
    return percent.toFixed(minDecimals) + '%';
}

/**
 * Simple event emitter mixin.
 * @returns {object} Event emitter methods
 */
export function createEventEmitter() {
    const callbacks = {};

    return {
        on(event, callback) {
            if (!callbacks[event]) callbacks[event] = [];
            callbacks[event].push(callback);
        },

        off(event, callback) {
            if (!callbacks[event]) return;
            callbacks[event] = callbacks[event].filter(cb => cb !== callback);
        },

        emit(event, data) {
            if (!callbacks[event]) return;
            callbacks[event].forEach(cb => cb(data));
        }
    };
}

/**
 * Create a debounced function.
 * @param {Function} fn - Function to debounce
 * @param {number} delay - Delay in milliseconds
 * @returns {Function} Debounced function
 */
export function debounce(fn, delay = 100) {
    let timeout;
    return (...args) => {
        clearTimeout(timeout);
        timeout = setTimeout(() => fn(...args), delay);
    };
}

/**
 * Create a throttled function.
 * @param {Function} fn - Function to throttle
 * @param {number} limit - Minimum time between calls
 * @returns {Function} Throttled function
 */
export function throttle(fn, limit = 100) {
    let inThrottle;
    return (...args) => {
        if (!inThrottle) {
            fn(...args);
            inThrottle = true;
            setTimeout(() => inThrottle = false, limit);
        }
    };
}
