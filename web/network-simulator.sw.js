/**
 * ServiceWorker for Network Simulation
 *
 * Intercepts network requests to simulate packet loss, delays, and
 * protocol-specific retry behavior for realistic performance testing.
 *
 * This enables browser-based simulation of:
 * - Lossy channels (configurable loss rate)
 * - Network delays and jitter
 * - Protocol-specific retry logic (TCP, QUIC, TGP)
 * - Throughput and timing metrics
 */

// Global configuration
let simulationConfig = {
    enabled: false,
    lossRate: 0.5, // 50% default
    minDelay: 10,  // ms
    maxDelay: 50,  // ms
    protocol: 'tgp' // 'tcp', 'quic', 'udp', 'tgp'
};

// Metrics tracking
const metrics = {
    totalRequests: 0,
    successfulRequests: 0,
    lostPackets: 0,
    retriedPackets: 0,
    totalDelay: 0,
    startTime: null
};

/**
 * Install event - activate immediately
 */
self.addEventListener('install', (event) => {
    console.log('[NetworkSimulator SW] Installing...');
    self.skipWaiting();
});

/**
 * Activate event - take control immediately
 */
self.addEventListener('activate', (event) => {
    console.log('[NetworkSimulator SW] Activating...');
    event.waitUntil(self.clients.claim());
});

/**
 * Message handler for configuration updates
 */
self.addEventListener('message', (event) => {
    const { type, data } = event.data;

    switch (type) {
        case 'CONFIG':
            simulationConfig = { ...simulationConfig, ...data };
            console.log('[NetworkSimulator SW] Config updated:', simulationConfig);
            if (event.ports && event.ports[0]) {
                event.ports[0].postMessage({ type: 'CONFIG_OK' });
            }
            break;

        case 'START_SIMULATION':
            simulationConfig.enabled = true;
            simulationConfig.protocol = data.protocol;
            simulationConfig.lossRate = data.lossRate;
            resetMetrics();
            console.log(`[NetworkSimulator SW] Started ${data.protocol.toUpperCase()} simulation at ${data.lossRate * 100}% loss`);
            if (event.ports && event.ports[0]) {
                event.ports[0].postMessage({ type: 'SIMULATION_STARTED', success: true });
            }
            break;

        case 'STOP_SIMULATION':
            simulationConfig.enabled = false;
            const finalMetrics = getMetrics();
            console.log('[NetworkSimulator SW] Stopped simulation');
            if (event.ports && event.ports[0]) {
                event.ports[0].postMessage({
                    type: 'SIMULATION_STOPPED',
                    success: true,
                    metrics: finalMetrics
                });
            }
            break;

        case 'RESET_METRICS':
            resetMetrics();
            if (event.ports && event.ports[0]) {
                event.ports[0].postMessage({ type: 'METRICS_RESET' });
            }
            break;

        case 'GET_METRICS':
            if (event.ports && event.ports[0]) {
                event.ports[0].postMessage({
                    type: 'METRICS',
                    data: getMetrics()
                });
            }
            break;

        default:
            console.warn('[NetworkSimulator SW] Unknown message type:', type);
    }
});

/**
 * Fetch event - intercept network requests for simulation
 */
self.addEventListener('fetch', (event) => {
    const url = new URL(event.request.url);

    // Only intercept requests to our simulation endpoint
    if (!url.pathname.startsWith('/api/sim/')) {
        return; // Pass through
    }

    if (!simulationConfig.enabled) {
        // Simulation disabled - pass through
        return event.respondWith(fetch(event.request));
    }

    // Simulate the request based on protocol
    event.respondWith(handleSimulatedRequest(event.request));
});

/**
 * Handle a simulated network request
 */
async function handleSimulatedRequest(request) {
    metrics.totalRequests++;

    if (metrics.startTime === null) {
        metrics.startTime = Date.now();
    }

    // Determine if packet is lost
    const isLost = Math.random() < simulationConfig.lossRate;

    if (isLost) {
        metrics.lostPackets++;

        // Protocol-specific retry behavior
        const shouldRetry = await handleProtocolRetry(request);

        if (!shouldRetry) {
            // Packet lost, no retry - return error
            return new Response(JSON.stringify({
                success: false,
                error: 'PACKET_LOST',
                metrics: getMetrics()
            }), {
                status: 503,
                headers: { 'Content-Type': 'application/json' }
            });
        }

        metrics.retriedPackets++;
        // Continue to delivery after retry
    }

    // Simulate network delay
    const delay = simulationConfig.minDelay +
                  Math.random() * (simulationConfig.maxDelay - simulationConfig.minDelay);

    metrics.totalDelay += delay;
    await sleep(delay);

    // Successfully deliver the packet
    metrics.successfulRequests++;

    return new Response(JSON.stringify({
        success: true,
        protocol: simulationConfig.protocol,
        delay: delay,
        retried: isLost,
        metrics: getMetrics()
    }), {
        status: 200,
        headers: { 'Content-Type': 'application/json' }
    });
}

/**
 * Protocol-specific retry logic
 */
async function handleProtocolRetry(request) {
    const protocol = simulationConfig.protocol;

    switch (protocol) {
        case 'tcp':
            // TCP: Exponential backoff retry
            // Try up to 3 times with increasing delays
            for (let attempt = 0; attempt < 3; attempt++) {
                const backoffDelay = Math.pow(2, attempt) * 100; // 100ms, 200ms, 400ms
                await sleep(backoffDelay);

                // Check if retry succeeds (same loss rate applies)
                if (Math.random() >= simulationConfig.lossRate) {
                    return true; // Retry succeeded
                }
            }
            return false; // All retries failed

        case 'quic':
            // QUIC: Faster retry with selective ACK
            // Try up to 2 times with shorter delays
            for (let attempt = 0; attempt < 2; attempt++) {
                await sleep(50); // Quick retry

                if (Math.random() >= simulationConfig.lossRate) {
                    return true;
                }
            }
            return false;

        case 'tgp':
            // TGP: Continuous flooding - always retries
            // Keep retrying until success
            let attempts = 0;
            while (attempts < 100) { // Reasonable limit to prevent infinite loop
                await sleep(10); // Very fast continuous flooding

                if (Math.random() >= simulationConfig.lossRate) {
                    return true; // Eventually succeeds
                }
                attempts++;
            }
            // Even TGP can timeout after many attempts
            return attempts < 100;

        case 'udp':
        default:
            // UDP: No retry, fire and forget
            return false;
    }
}

/**
 * Reset metrics
 */
function resetMetrics() {
    metrics.totalRequests = 0;
    metrics.successfulRequests = 0;
    metrics.lostPackets = 0;
    metrics.retriedPackets = 0;
    metrics.totalDelay = 0;
    metrics.startTime = null;
}

/**
 * Get current metrics
 */
function getMetrics() {
    const elapsed = metrics.startTime ? (Date.now() - metrics.startTime) / 1000 : 0;

    return {
        totalRequests: metrics.totalRequests,
        successfulRequests: metrics.successfulRequests,
        lostPackets: metrics.lostPackets,
        retriedPackets: metrics.retriedPackets,
        lossRate: metrics.totalRequests > 0
            ? (metrics.lostPackets / metrics.totalRequests * 100).toFixed(2)
            : 0,
        avgDelay: metrics.successfulRequests > 0
            ? (metrics.totalDelay / metrics.successfulRequests).toFixed(2)
            : 0,
        throughput: elapsed > 0
            ? (metrics.successfulRequests / elapsed).toFixed(2)
            : 0,
        elapsed: elapsed.toFixed(2)
    };
}

/**
 * Utility: Sleep for specified milliseconds
 */
function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

console.log('[NetworkSimulator SW] Loaded and ready');
