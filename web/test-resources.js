/**
 * Test Resource Generator
 * Generates test resources for network simulation and protocol comparison
 */

export class TestResourceGenerator {
    constructor() {
        this.resources = new Map();
    }

    /**
     * Generate a test image URL for packet loss testing
     */
    generateTestImageURL(size = '100x100', seed = Math.random()) {
        // Use a simple data URI for testing (avoids external dependencies)
        return this.createTestDataURI(size, seed);
    }

    /**
     * Create a data URI for testing
     */
    createTestDataURI(size, seed) {
        const [width, height] = size.split('x').map(Number);

        // Create a simple pattern based on seed
        const canvas = document.createElement('canvas');
        canvas.width = width;
        canvas.height = height;

        const ctx = canvas.getContext('2d');

        // Fill with gradient based on seed
        const gradient = ctx.createLinearGradient(0, 0, width, height);
        gradient.addColorStop(0, `hsl(${seed * 360}, 70%, 50%)`);
        gradient.addColorStop(1, `hsl(${(seed * 360 + 180) % 360}, 70%, 30%)`);

        ctx.fillStyle = gradient;
        ctx.fillRect(0, 0, width, height);

        // Add some text
        ctx.fillStyle = '#fff';
        ctx.font = '14px monospace';
        ctx.textAlign = 'center';
        ctx.fillText(`Test ${Math.floor(seed * 1000)}`, width / 2, height / 2);

        return canvas.toDataURL('image/png');
    }

    /**
     * Generate a test resource endpoint that will be intercepted by ServiceWorker
     */
    generateSimulatedResourceURL(resourceId, protocol, size = 1024) {
        // This URL will be intercepted by the ServiceWorker
        return `/test-resource/${protocol}/${resourceId}?size=${size}&t=${Date.now()}`;
    }

    /**
     * Create a mock server endpoint for testing
     * Returns a function that handles requests
     */
    createMockEndpoint(delay = 100, failureRate = 0) {
        return async (request) => {
            // Simulate network delay
            await this.delay(delay);

            // Simulate random failures
            if (Math.random() < failureRate) {
                throw new Error('Network failure');
            }

            // Return successful response
            return {
                status: 200,
                data: {
                    timestamp: Date.now(),
                    request: request.url
                }
            };
        };
    }

    /**
     * Generate test data of specified size
     */
    generateTestData(sizeBytes) {
        const data = new Uint8Array(sizeBytes);
        for (let i = 0; i < sizeBytes; i++) {
            data[i] = Math.floor(Math.random() * 256);
        }
        return data;
    }

    /**
     * Helper: delay
     */
    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}

/**
 * Image Loading Test Runner
 * Tests image loading performance across different protocols
 */
export class ImageLoadingTestRunner {
    constructor(imageContainer) {
        this.container = imageContainer;
        this.resourceGenerator = new TestResourceGenerator();
        this.results = [];
    }

    /**
     * Run image loading test for a specific protocol
     */
    async runTest(protocol, lossRate, imageCount = 10) {
        const results = {
            protocol,
            lossRate,
            images: [],
            totalTime: 0,
            successCount: 0,
            failureCount: 0
        };

        const startTime = performance.now();

        // Create test images
        const imagePromises = [];

        for (let i = 0; i < imageCount; i++) {
            const promise = this.loadTestImage(protocol, i, lossRate);
            imagePromises.push(promise);

            // Stagger image loads slightly
            await this.delay(50);
        }

        // Wait for all images
        const imageResults = await Promise.allSettled(imagePromises);

        imageResults.forEach((result, index) => {
            if (result.status === 'fulfilled') {
                results.images.push(result.value);
                if (result.value.success) {
                    results.successCount++;
                } else {
                    results.failureCount++;
                }
            } else {
                results.failureCount++;
                results.images.push({
                    index,
                    success: false,
                    error: result.reason.message,
                    loadTime: 0
                });
            }
        });

        const endTime = performance.now();
        results.totalTime = endTime - startTime;

        this.results.push(results);
        return results;
    }

    /**
     * Load a single test image
     */
    async loadTestImage(protocol, index, lossRate) {
        return new Promise((resolve, reject) => {
            const img = new Image();
            const startTime = performance.now();

            // Create test resource URL (will be intercepted by ServiceWorker)
            const url = this.resourceGenerator.generateSimulatedResourceURL(
                `image-${index}`,
                protocol
            );

            img.onload = () => {
                const endTime = performance.now();
                const loadTime = endTime - startTime;

                // Add to container
                if (this.container) {
                    this.container.appendChild(img);
                    img.classList.add('test-image', `protocol-${protocol}`);
                    img.title = `${protocol.toUpperCase()}: ${loadTime.toFixed(0)}ms`;
                }

                resolve({
                    index,
                    protocol,
                    success: true,
                    loadTime,
                    url
                });
            };

            img.onerror = () => {
                const endTime = performance.now();
                const loadTime = endTime - startTime;

                resolve({
                    index,
                    protocol,
                    success: false,
                    loadTime,
                    url,
                    error: 'Failed to load'
                });
            };

            // Set timeout
            const timeout = setTimeout(() => {
                reject(new Error('Image load timeout'));
            }, 30000);

            img.onload = () => {
                clearTimeout(timeout);
                img.onload();
            };

            // Trigger load
            img.src = url;
        });
    }

    /**
     * Run comparison test across all protocols
     */
    async runComparison(lossRates = [0.1, 0.5, 0.9], imageCount = 10) {
        const protocols = ['tcp', 'quic', 'tgp'];
        const comparison = [];

        for (const lossRate of lossRates) {
            console.log(`\n=== Testing at ${lossRate * 100}% packet loss ===`);

            const lossRateResults = {
                lossRate,
                protocols: []
            };

            for (const protocol of protocols) {
                const result = await this.runTest(protocol, lossRate, imageCount);
                lossRateResults.protocols.push(result);

                console.log(`${protocol.toUpperCase()}: ${result.successCount}/${imageCount} loaded in ${result.totalTime.toFixed(0)}ms`);

                // Delay between protocol tests
                await this.delay(1000);
            }

            comparison.push(lossRateResults);

            // Clear container between loss rates
            if (this.container) {
                this.container.innerHTML = '';
            }

            // Delay between loss rate tests
            await this.delay(2000);
        }

        return comparison;
    }

    /**
     * Get test summary
     */
    getSummary() {
        const summary = {
            totalTests: this.results.length,
            byProtocol: {}
        };

        this.results.forEach(result => {
            if (!summary.byProtocol[result.protocol]) {
                summary.byProtocol[result.protocol] = {
                    tests: 0,
                    totalImages: 0,
                    successfulImages: 0,
                    avgLoadTime: 0,
                    successRate: 0
                };
            }

            const protocolSummary = summary.byProtocol[result.protocol];
            protocolSummary.tests++;
            protocolSummary.totalImages += result.images.length;
            protocolSummary.successfulImages += result.successCount;

            const successfulLoads = result.images.filter(img => img.success);
            if (successfulLoads.length > 0) {
                const avgTime = successfulLoads.reduce((sum, img) => sum + img.loadTime, 0) / successfulLoads.length;
                protocolSummary.avgLoadTime += avgTime;
            }
        });

        // Calculate averages
        Object.values(summary.byProtocol).forEach(ps => {
            ps.successRate = ps.totalImages > 0
                ? (ps.successfulImages / ps.totalImages * 100).toFixed(1)
                : 0;
            ps.avgLoadTime = ps.tests > 0
                ? (ps.avgLoadTime / ps.tests).toFixed(1)
                : 0;
        });

        return summary;
    }

    /**
     * Clear all results
     */
    clearResults() {
        this.results = [];
        if (this.container) {
            this.container.innerHTML = '';
        }
    }

    /**
     * Helper: delay
     */
    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}

/**
 * Throughput Measurement
 * Measures actual throughput under different loss conditions
 */
export class ThroughputMeasurement {
    constructor() {
        this.measurements = [];
    }

    /**
     * Measure throughput for a specific protocol
     */
    async measureThroughput(protocol, lossRate, duration = 10000) {
        const startTime = performance.now();
        const endTime = startTime + duration;

        let requests = 0;
        let successes = 0;
        let failures = 0;
        let totalBytes = 0;

        while (performance.now() < endTime) {
            requests++;

            try {
                const url = `/test-resource/${protocol}/chunk-${requests}?size=1024`;
                const response = await fetch(url);

                if (response.ok) {
                    successes++;
                    const blob = await response.blob();
                    totalBytes += blob.size;
                } else {
                    failures++;
                }
            } catch (error) {
                failures++;
            }

            // Small delay to prevent overwhelming the system
            await this.delay(10);
        }

        const actualDuration = performance.now() - startTime;

        const measurement = {
            protocol,
            lossRate,
            duration: actualDuration,
            requests,
            successes,
            failures,
            totalBytes,
            throughputBps: (totalBytes * 8 * 1000) / actualDuration,
            throughputKbps: ((totalBytes * 8 * 1000) / actualDuration) / 1024,
            requestsPerSecond: (successes * 1000) / actualDuration,
            successRate: (successes / requests) * 100
        };

        this.measurements.push(measurement);
        return measurement;
    }

    /**
     * Run throughput comparison
     */
    async runComparison(lossRates, duration = 5000) {
        const protocols = ['tcp', 'quic', 'tgp'];
        const results = [];

        for (const lossRate of lossRates) {
            for (const protocol of protocols) {
                console.log(`Measuring ${protocol.toUpperCase()} at ${lossRate * 100}% loss...`);

                const measurement = await this.measureThroughput(protocol, lossRate, duration);
                results.push(measurement);

                console.log(`  Throughput: ${measurement.throughputKbps.toFixed(2)} Kbps`);
                console.log(`  Success rate: ${measurement.successRate.toFixed(1)}%`);

                // Delay between tests
                await this.delay(1000);
            }
        }

        return results;
    }

    /**
     * Get measurement summary
     */
    getSummary() {
        const byProtocol = {};

        this.measurements.forEach(m => {
            if (!byProtocol[m.protocol]) {
                byProtocol[m.protocol] = {
                    measurements: 0,
                    avgThroughput: 0,
                    maxThroughput: 0,
                    avgSuccessRate: 0
                };
            }

            const summary = byProtocol[m.protocol];
            summary.measurements++;
            summary.avgThroughput += m.throughputKbps;
            summary.maxThroughput = Math.max(summary.maxThroughput, m.throughputKbps);
            summary.avgSuccessRate += m.successRate;
        });

        // Calculate averages
        Object.values(byProtocol).forEach(s => {
            s.avgThroughput = (s.avgThroughput / s.measurements).toFixed(2);
            s.avgSuccessRate = (s.avgSuccessRate / s.measurements).toFixed(1);
        });

        return byProtocol;
    }

    /**
     * Helper: delay
     */
    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}
