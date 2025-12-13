/**
 * Network Simulation Manager
 * Manages ServiceWorker-based network simulation for realistic protocol comparisons
 */

export class NetworkSimulationManager {
    constructor() {
        this.serviceWorker = null;
        this.isRegistered = false;
        this.currentSimulation = null;
    }

    /**
     * Initialize and register the ServiceWorker
     */
    async initialize() {
        if (!('serviceWorker' in navigator)) {
            throw new Error('ServiceWorker not supported in this browser');
        }

        try {
            const registration = await navigator.serviceWorker.register(
                '/network-simulator.sw.js',
                { scope: '/' }
            );

            // Wait for the ServiceWorker to become active
            await this.waitForActive(registration);

            this.serviceWorker = registration.active;
            this.isRegistered = true;

            console.log('Network simulation ServiceWorker registered');
            return true;
        } catch (error) {
            console.error('Failed to register ServiceWorker:', error);
            throw error;
        }
    }

    /**
     * Wait for ServiceWorker to become active
     */
    async waitForActive(registration) {
        return new Promise((resolve) => {
            if (registration.active) {
                resolve();
                return;
            }

            const worker = registration.installing || registration.waiting;
            if (worker) {
                worker.addEventListener('statechange', () => {
                    if (worker.state === 'activated') {
                        resolve();
                    }
                });
            }
        });
    }

    /**
     * Send message to ServiceWorker and wait for response
     */
    async sendMessage(type, data = {}) {
        if (!this.serviceWorker) {
            throw new Error('ServiceWorker not initialized');
        }

        return new Promise((resolve, reject) => {
            const messageChannel = new MessageChannel();

            messageChannel.port1.onmessage = (event) => {
                if (event.data.error) {
                    reject(new Error(event.data.error));
                } else {
                    resolve(event.data);
                }
            };

            this.serviceWorker.postMessage(
                { type, data },
                [messageChannel.port2]
            );
        });
    }

    /**
     * Start a network simulation
     */
    async startSimulation(protocol, lossRate) {
        if (!this.isRegistered) {
            await this.initialize();
        }

        const response = await this.sendMessage('START_SIMULATION', {
            protocol,
            lossRate
        });

        this.currentSimulation = { protocol, lossRate };
        return response;
    }

    /**
     * Stop the current simulation and get metrics
     */
    async stopSimulation() {
        const response = await this.sendMessage('STOP_SIMULATION');
        this.currentSimulation = null;
        return response;
    }

    /**
     * Get current metrics without stopping
     */
    async getMetrics() {
        const response = await this.sendMessage('GET_METRICS');
        return response.metrics;
    }

    /**
     * Reset metrics
     */
    async resetMetrics() {
        return await this.sendMessage('RESET_METRICS');
    }

    /**
     * Simulate fetching a resource with the current protocol
     */
    async simulateFetch(resourceUrl, options = {}) {
        if (!this.currentSimulation) {
            throw new Error('No simulation active');
        }

        const startTime = performance.now();

        try {
            const response = await fetch(resourceUrl, options);
            const endTime = performance.now();

            return {
                success: true,
                duration: endTime - startTime,
                response
            };
        } catch (error) {
            const endTime = performance.now();

            return {
                success: false,
                duration: endTime - startTime,
                error: error.message
            };
        }
    }
}

/**
 * Protocol Comparison Runner
 * Runs multiple protocols against the same test and compares results
 */
export class ProtocolComparisonRunner {
    constructor() {
        this.simulator = new NetworkSimulationManager();
        this.results = [];
    }

    /**
     * Run comparison test for all protocols at a specific loss rate
     */
    async runComparison(lossRate, testResourceUrl, options = {}) {
        const protocols = ['tcp', 'quic', 'tgp'];
        const results = [];

        for (const protocol of protocols) {
            console.log(`Testing ${protocol.toUpperCase()} at ${lossRate * 100}% loss...`);

            // Start simulation with this protocol
            await this.simulator.startSimulation(protocol, lossRate);
            await this.simulator.resetMetrics();

            const startTime = performance.now();

            // Run the test (multiple fetches)
            const attempts = options.attempts || 10;
            const fetchResults = [];

            for (let i = 0; i < attempts; i++) {
                const result = await this.simulator.simulateFetch(
                    `${testResourceUrl}?protocol=${protocol}&attempt=${i}`
                );
                fetchResults.push(result);

                // Small delay between attempts
                await this.delay(options.delayBetweenAttempts || 50);
            }

            const endTime = performance.now();

            // Get metrics
            const metrics = await this.simulator.getMetrics();

            // Stop simulation
            await this.simulator.stopSimulation();

            // Compile results
            const protocolResult = {
                protocol: protocol.toUpperCase(),
                lossRate,
                totalDuration: endTime - startTime,
                attempts: metrics.attempts,
                successes: metrics.successes,
                failures: metrics.failures,
                retries: metrics.retries,
                avgLatency: metrics.successes > 0
                    ? metrics.totalLatency / metrics.successes
                    : 0,
                successRate: metrics.attempts > 0
                    ? (metrics.successes / attempts) * 100
                    : 0,
                throughput: this.calculateThroughput(
                    metrics.successes,
                    endTime - startTime
                ),
                efficiency: metrics.attempts > 0
                    ? (metrics.successes / metrics.attempts) * 100
                    : 0
            };

            results.push(protocolResult);
            this.results.push(protocolResult);
        }

        return results;
    }

    /**
     * Run comparison across multiple loss rates
     */
    async runFullComparison(lossRates, testResourceUrl, options = {}) {
        const allResults = [];

        for (const lossRate of lossRates) {
            console.log(`\n=== Testing at ${lossRate * 100}% packet loss ===`);

            const results = await this.runComparison(lossRate, testResourceUrl, options);
            allResults.push({
                lossRate,
                results
            });

            // Delay between loss rate tests
            await this.delay(options.delayBetweenTests || 500);
        }

        return allResults;
    }

    /**
     * Calculate throughput (successful fetches per second)
     */
    calculateThroughput(successes, durationMs) {
        return (successes / (durationMs / 1000)).toFixed(2);
    }

    /**
     * Get comparison summary
     */
    getSummary() {
        const byProtocol = {};

        this.results.forEach(result => {
            if (!byProtocol[result.protocol]) {
                byProtocol[result.protocol] = {
                    protocol: result.protocol,
                    tests: 0,
                    avgSuccessRate: 0,
                    avgLatency: 0,
                    avgThroughput: 0,
                    totalRetries: 0
                };
            }

            const summary = byProtocol[result.protocol];
            summary.tests++;
            summary.avgSuccessRate += result.successRate;
            summary.avgLatency += result.avgLatency;
            summary.avgThroughput += parseFloat(result.throughput);
            summary.totalRetries += result.retries;
        });

        // Calculate averages
        Object.values(byProtocol).forEach(summary => {
            summary.avgSuccessRate = (summary.avgSuccessRate / summary.tests).toFixed(1);
            summary.avgLatency = (summary.avgLatency / summary.tests).toFixed(1);
            summary.avgThroughput = (summary.avgThroughput / summary.tests).toFixed(2);
        });

        return byProtocol;
    }

    /**
     * Clear all results
     */
    clearResults() {
        this.results = [];
    }

    /**
     * Helper: delay
     */
    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}

/**
 * Performance Chart Data Generator
 * Generates data suitable for D3 charts
 */
export class PerformanceChartDataGenerator {
    constructor(comparisonResults) {
        this.comparisonResults = comparisonResults;
    }

    /**
     * Generate data for throughput vs loss rate chart
     */
    getThroughputData() {
        const data = [];

        this.comparisonResults.forEach(({ lossRate, results }) => {
            results.forEach(result => {
                data.push({
                    lossRate: lossRate * 100,
                    protocol: result.protocol,
                    throughput: parseFloat(result.throughput)
                });
            });
        });

        return data;
    }

    /**
     * Generate data for latency comparison chart
     */
    getLatencyData() {
        const data = [];

        this.comparisonResults.forEach(({ lossRate, results }) => {
            results.forEach(result => {
                data.push({
                    lossRate: lossRate * 100,
                    protocol: result.protocol,
                    latency: result.avgLatency
                });
            });
        });

        return data;
    }

    /**
     * Generate data for success rate chart
     */
    getSuccessRateData() {
        const data = [];

        this.comparisonResults.forEach(({ lossRate, results }) => {
            results.forEach(result => {
                data.push({
                    lossRate: lossRate * 100,
                    protocol: result.protocol,
                    successRate: result.successRate
                });
            });
        });

        return data;
    }

    /**
     * Generate data for retry efficiency chart
     */
    getRetryEfficiencyData() {
        const data = [];

        this.comparisonResults.forEach(({ lossRate, results }) => {
            results.forEach(result => {
                data.push({
                    lossRate: lossRate * 100,
                    protocol: result.protocol,
                    efficiency: result.efficiency,
                    retries: result.retries
                });
            });
        });

        return data;
    }

    /**
     * Generate grouped bar chart data
     */
    getGroupedBarData(metric = 'throughput') {
        const grouped = {};

        this.comparisonResults.forEach(({ lossRate, results }) => {
            const key = `${lossRate * 100}%`;
            if (!grouped[key]) {
                grouped[key] = { lossRate: key, values: {} };
            }

            results.forEach(result => {
                grouped[key].values[result.protocol] = result[metric];
            });
        });

        return Object.values(grouped);
    }
}
