/**
 * ServiceWorker for realistic network simulation
 * Intercepts fetch requests to simulate packet loss and protocol-specific retry logic
 */

// Simulation state
let simulationConfig = {
  enabled: false,
  lossRate: 0,
  protocol: 'none', // 'tcp', 'quic', 'tgp'
  metrics: {
    attempts: 0,
    successes: 0,
    failures: 0,
    totalLatency: 0,
    retries: 0
  }
};

// Protocol-specific retry configurations
const RETRY_CONFIGS = {
  tcp: {
    maxRetries: 10,
    initialTimeout: 100,
    maxTimeout: 60000,
    backoffMultiplier: 2
  },
  quic: {
    maxRetries: 5,
    initialTimeout: 50,
    maxTimeout: 10000,
    backoffMultiplier: 1.5
  },
  tgp: {
    floodInterval: 10, // Continuous flooding every 10ms
    maxDuration: 5000  // Stop after 5 seconds
  }
};

/**
 * TCP exponential backoff retry logic
 */
async function tcpFetch(request, config) {
  const startTime = performance.now();
  let attempt = 0;
  let timeout = config.initialTimeout;

  while (attempt < config.maxRetries) {
    attempt++;
    simulationConfig.metrics.attempts++;

    // Simulate packet loss
    const random = Math.random();
    if (random >= simulationConfig.lossRate) {
      // Success
      try {
        const response = await fetch(request.clone());
        const endTime = performance.now();
        simulationConfig.metrics.successes++;
        simulationConfig.metrics.totalLatency += (endTime - startTime);
        if (attempt > 1) {
          simulationConfig.metrics.retries += (attempt - 1);
        }
        return response;
      } catch (error) {
        // Network error (not packet loss)
        simulationConfig.metrics.failures++;
        throw error;
      }
    } else {
      // Packet lost
      simulationConfig.metrics.failures++;

      // Wait with exponential backoff
      await new Promise(resolve => setTimeout(resolve, timeout));
      timeout = Math.min(timeout * config.backoffMultiplier, config.maxTimeout);
    }
  }

  // Max retries exhausted
  throw new Error('TCP: Max retries exceeded');
}

/**
 * QUIC selective acknowledgment retry logic
 * Simulates more aggressive retransmission with faster recovery
 */
async function quicFetch(request, config) {
  const startTime = performance.now();
  let attempt = 0;
  let timeout = config.initialTimeout;

  // QUIC can send multiple packets in parallel and selective ACK
  // We simulate this with faster timeouts and more retries
  while (attempt < config.maxRetries) {
    attempt++;
    simulationConfig.metrics.attempts++;

    // Simulate packet loss
    const random = Math.random();
    if (random >= simulationConfig.lossRate) {
      // Success
      try {
        const response = await fetch(request.clone());
        const endTime = performance.now();
        simulationConfig.metrics.successes++;
        simulationConfig.metrics.totalLatency += (endTime - startTime);
        if (attempt > 1) {
          simulationConfig.metrics.retries += (attempt - 1);
        }
        return response;
      } catch (error) {
        simulationConfig.metrics.failures++;
        throw error;
      }
    } else {
      // Packet lost - QUIC recovers faster
      simulationConfig.metrics.failures++;

      // Wait with milder exponential backoff
      await new Promise(resolve => setTimeout(resolve, timeout));
      timeout = Math.min(timeout * config.backoffMultiplier, config.maxTimeout);
    }
  }

  throw new Error('QUIC: Max retries exceeded');
}

/**
 * TGP continuous flooding logic
 * Floods packets continuously until one succeeds or timeout
 */
async function tgpFetch(request, config) {
  const startTime = performance.now();

  return new Promise((resolve, reject) => {
    let resolved = false;
    let floodCount = 0;

    const floodInterval = setInterval(async () => {
      if (resolved) return;

      floodCount++;
      simulationConfig.metrics.attempts++;

      // Check timeout
      const elapsed = performance.now() - startTime;
      if (elapsed > config.maxDuration) {
        clearInterval(floodInterval);
        if (!resolved) {
          reject(new Error('TGP: Timeout exceeded'));
        }
        return;
      }

      // Simulate packet loss
      const random = Math.random();
      if (random >= simulationConfig.lossRate) {
        // Success - one packet got through
        try {
          const response = await fetch(request.clone());
          if (!resolved) {
            resolved = true;
            clearInterval(floodInterval);

            const endTime = performance.now();
            simulationConfig.metrics.successes++;
            simulationConfig.metrics.totalLatency += (endTime - startTime);
            if (floodCount > 1) {
              simulationConfig.metrics.retries += (floodCount - 1);
            }
            resolve(response);
          }
        } catch (error) {
          if (!resolved) {
            resolved = true;
            clearInterval(floodInterval);
            simulationConfig.metrics.failures++;
            reject(error);
          }
        }
      } else {
        // Packet lost - keep flooding
        simulationConfig.metrics.failures++;
      }
    }, config.floodInterval);
  });
}

/**
 * Handle fetch requests with simulation
 */
self.addEventListener('fetch', (event) => {
  const url = new URL(event.request.url);

  // Only intercept requests to test images/resources
  if (!simulationConfig.enabled || !url.pathname.includes('/test-resource')) {
    return event.respondWith(fetch(event.request));
  }

  // Apply protocol-specific retry logic
  let fetchPromise;

  switch (simulationConfig.protocol) {
    case 'tcp':
      fetchPromise = tcpFetch(event.request, RETRY_CONFIGS.tcp);
      break;
    case 'quic':
      fetchPromise = quicFetch(event.request, RETRY_CONFIGS.quic);
      break;
    case 'tgp':
      fetchPromise = tgpFetch(event.request, RETRY_CONFIGS.tgp);
      break;
    default:
      fetchPromise = fetch(event.request);
  }

  event.respondWith(fetchPromise);
});

/**
 * Handle messages from the page
 */
self.addEventListener('message', (event) => {
  const { type, data } = event.data;

  switch (type) {
    case 'START_SIMULATION':
      simulationConfig.enabled = true;
      simulationConfig.lossRate = data.lossRate;
      simulationConfig.protocol = data.protocol;
      simulationConfig.metrics = {
        attempts: 0,
        successes: 0,
        failures: 0,
        totalLatency: 0,
        retries: 0
      };
      event.ports[0].postMessage({ success: true });
      break;

    case 'STOP_SIMULATION':
      simulationConfig.enabled = false;
      event.ports[0].postMessage({
        success: true,
        metrics: simulationConfig.metrics
      });
      break;

    case 'GET_METRICS':
      event.ports[0].postMessage({
        metrics: simulationConfig.metrics
      });
      break;

    case 'RESET_METRICS':
      simulationConfig.metrics = {
        attempts: 0,
        successes: 0,
        failures: 0,
        totalLatency: 0,
        retries: 0
      };
      event.ports[0].postMessage({ success: true });
      break;
  }
});

// Install and activate
self.addEventListener('install', (event) => {
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil(self.clients.claim());
});
