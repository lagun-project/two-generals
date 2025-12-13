/**
 * Image Loading Comparison Test
 *
 * Demonstrates protocol performance by loading actual images/resources
 * through simulated lossy networks. Compares:
 * - TCP-like: Exponential backoff retry
 * - QUIC-like: Fast retry with selective ACK
 * - TGP: Continuous flooding
 * - UDP: Fire-and-forget (no retry)
 *
 * Uses the ServiceWorker network simulator for realistic packet loss.
 */

import * as d3 from 'd3';

/**
 * NetworkSimulatorClient - Communicates with the ServiceWorker
 */
class NetworkSimulatorClient {
    constructor() {
        this.sw = null;
        this.ready = false;
        this.messageChannel = null;
    }

    /**
     * Register and activate the ServiceWorker
     */
    async register() {
        if (!('serviceWorker' in navigator)) {
            throw new Error('ServiceWorker not supported');
        }

        try {
            const registration = await navigator.serviceWorker.register(
                '/network-simulator.sw.js',
                { scope: '/' }
            );

            await navigator.serviceWorker.ready;
            this.sw = registration.active || registration.installing || registration.waiting;
            this.ready = true;

            console.log('[ImageLoadingTest] ServiceWorker registered');
            return true;
        } catch (error) {
            console.error('[ImageLoadingTest] ServiceWorker registration failed:', error);
            throw error;
        }
    }

    /**
     * Configure the simulation
     */
    async configure(config) {
        if (!this.ready) {
            throw new Error('ServiceWorker not ready');
        }

        const messageChannel = new MessageChannel();

        return new Promise((resolve, reject) => {
            messageChannel.port1.onmessage = (event) => {
                if (event.data.type === 'CONFIG_OK') {
                    resolve(true);
                } else {
                    reject(new Error('Config failed'));
                }
            };

            navigator.serviceWorker.controller.postMessage({
                type: 'CONFIG',
                data: config
            }, [messageChannel.port2]);

            // Timeout after 5 seconds
            setTimeout(() => reject(new Error('Config timeout')), 5000);
        });
    }

    /**
     * Get metrics from the ServiceWorker
     */
    async getMetrics() {
        const messageChannel = new MessageChannel();

        return new Promise((resolve) => {
            messageChannel.port1.onmessage = (event) => {
                resolve(event.data);
            };

            navigator.serviceWorker.controller.postMessage({
                type: 'GET_METRICS'
            }, [messageChannel.port2]);
        });
    }

    /**
     * Reset metrics
     */
    async resetMetrics() {
        const messageChannel = new MessageChannel();

        return new Promise((resolve) => {
            messageChannel.port1.onmessage = (event) => {
                resolve(event.data);
            };

            navigator.serviceWorker.controller.postMessage({
                type: 'RESET_METRICS'
            }, [messageChannel.port2]);
        });
    }
}

/**
 * Image Loading Test Controller
 */
export class ImageLoadingTest {
    constructor(containerId) {
        this.container = d3.select(`#${containerId}`);
        this.simulator = new NetworkSimulatorClient();
        this.results = new Map();

        this.protocols = [
            { id: 'tgp', name: 'TGP', color: '#3fb950' },
            { id: 'tcp', name: 'TCP', color: '#f85149' },
            { id: 'quic', name: 'QUIC', color: '#58a6ff' },
            { id: 'udp', name: 'UDP', color: '#d29922' }
        ];
    }

    /**
     * Initialize the test interface
     */
    async init() {
        try {
            // Register ServiceWorker
            await this.simulator.register();

            // Render UI
            this.renderUI();

            console.log('[ImageLoadingTest] Initialized');
        } catch (error) {
            console.error('[ImageLoadingTest] Initialization failed:', error);
            this.container.html(`
                <div class="error-message">
                    <h3>ServiceWorker Not Available</h3>
                    <p>This test requires ServiceWorker support. Please use a modern browser (Chrome, Firefox, Edge).</p>
                    <p>Error: ${error.message}</p>
                </div>
            `);
        }
    }

    /**
     * Render the test UI
     */
    renderUI() {
        this.container.html('');

        // Header
        this.container.append('div')
            .attr('class', 'image-test-header')
            .html(`
                <h3>Real-World Image Loading Test</h3>
                <p>Compare protocol performance by loading actual resources through simulated packet loss</p>
            `);

        // Controls
        const controls = this.container.append('div')
            .attr('class', 'image-test-controls');

        controls.append('div')
            .attr('class', 'control-group')
            .html(`
                <label for="image-test-loss">Packet Loss Rate</label>
                <select id="image-test-loss">
                    <option value="0.1">10%</option>
                    <option value="0.3">30%</option>
                    <option value="0.5" selected>50%</option>
                    <option value="0.7">70%</option>
                    <option value="0.9">90%</option>
                </select>
            `);

        controls.append('div')
            .attr('class', 'control-group')
            .html(`
                <label for="image-test-size">Resource Size</label>
                <select id="image-test-size">
                    <option value="small">Small (~10KB)</option>
                    <option value="medium" selected>Medium (~100KB)</option>
                    <option value="large">Large (~1MB)</option>
                </select>
            `);

        controls.append('button')
            .attr('id', 'run-image-test')
            .attr('class', 'primary')
            .text('Run Image Loading Test')
            .on('click', () => this.runTest());

        // Results grid
        this.container.append('div')
            .attr('id', 'image-test-results')
            .attr('class', 'image-test-results');

        // Chart
        this.container.append('div')
            .attr('id', 'image-test-chart')
            .attr('class', 'image-test-chart');
    }

    /**
     * Run the image loading test
     */
    async runTest() {
        const lossRate = parseFloat(document.getElementById('image-test-loss').value);
        const size = document.getElementById('image-test-size').value;

        const resultsContainer = d3.select('#image-test-results');
        resultsContainer.html('<div class="loading">Running tests...</div>');

        this.results.clear();

        // Run test for each protocol
        for (const protocol of this.protocols) {
            const result = await this.testProtocol(protocol.id, lossRate, size);
            this.results.set(protocol.id, result);

            // Update display after each protocol
            this.renderResults();
        }

        // Render final chart
        this.renderChart();
    }

    /**
     * Test a specific protocol
     */
    async testProtocol(protocolId, lossRate, size) {
        // Configure simulator
        await this.simulator.configure({
            enabled: true,
            lossRate: lossRate,
            protocol: protocolId
        });

        await this.simulator.resetMetrics();

        const startTime = performance.now();

        // Create a test resource URL
        const resourceUrl = `/api/sim/test-resource?size=${size}&protocol=${protocolId}&t=${Date.now()}`;

        try {
            // Attempt to fetch the resource
            const response = await fetch(resourceUrl);

            if (!response.ok) {
                throw new Error(`HTTP ${response.status}`);
            }

            const data = await response.json();
            const endTime = performance.now();

            // Get metrics from ServiceWorker
            const metricsData = await this.simulator.getMetrics();

            return {
                success: true,
                duration: endTime - startTime,
                metrics: metricsData,
                data: data
            };
        } catch (error) {
            const endTime = performance.now();

            // Get metrics even on failure
            const metricsData = await this.simulator.getMetrics();

            return {
                success: false,
                duration: endTime - startTime,
                error: error.message,
                metrics: metricsData
            };
        }
    }

    /**
     * Render test results
     */
    renderResults() {
        const resultsContainer = d3.select('#image-test-results');
        resultsContainer.html('');

        // Create cards for each protocol
        for (const protocol of this.protocols) {
            const result = this.results.get(protocol.id);

            if (!result) continue;

            const card = resultsContainer.append('div')
                .attr('class', `protocol-result-card ${protocol.id} ${result.success ? 'success' : 'failure'}`);

            card.append('h4')
                .style('color', protocol.color)
                .text(protocol.name);

            if (result.success) {
                card.append('div')
                    .attr('class', 'result-metric')
                    .html(`
                        <span class="metric-label">Status</span>
                        <span class="metric-value success">✓ SUCCESS</span>
                    `);

                card.append('div')
                    .attr('class', 'result-metric')
                    .html(`
                        <span class="metric-label">Duration</span>
                        <span class="metric-value">${result.duration.toFixed(0)}ms</span>
                    `);

                if (result.data && result.data.metrics) {
                    const m = result.data.metrics;

                    card.append('div')
                        .attr('class', 'result-metric')
                        .html(`
                            <span class="metric-label">Attempts</span>
                            <span class="metric-value">${m.totalRequests}</span>
                        `);

                    card.append('div')
                        .attr('class', 'result-metric')
                        .html(`
                            <span class="metric-label">Success Rate</span>
                            <span class="metric-value">${((m.successfulRequests / m.totalRequests) * 100).toFixed(1)}%</span>
                        `);

                    if (result.data.retried) {
                        card.append('div')
                            .attr('class', 'result-badge')
                            .text('Recovered from packet loss');
                    }
                }
            } else {
                card.append('div')
                    .attr('class', 'result-metric')
                    .html(`
                        <span class="metric-label">Status</span>
                        <span class="metric-value failure">✗ FAILED</span>
                    `);

                card.append('div')
                    .attr('class', 'result-metric')
                    .html(`
                        <span class="metric-label">Error</span>
                        <span class="metric-value">${result.error || 'Timeout'}</span>
                    `);

                card.append('div')
                    .attr('class', 'result-metric')
                    .html(`
                        <span class="metric-label">Attempted Duration</span>
                        <span class="metric-value">${result.duration.toFixed(0)}ms</span>
                    `);
            }
        }
    }

    /**
     * Render comparison chart
     */
    renderChart() {
        const chartContainer = d3.select('#image-test-chart');
        chartContainer.html('');

        const margin = { top: 40, right: 120, bottom: 60, left: 80 };
        const width = 800 - margin.left - margin.right;
        const height = 400 - margin.top - margin.bottom;

        const svg = chartContainer.append('svg')
            .attr('viewBox', `0 0 ${width + margin.left + margin.right} ${height + margin.top + margin.bottom}`)
            .attr('class', 'image-test-chart-svg');

        const g = svg.append('g')
            .attr('transform', `translate(${margin.left},${margin.top})`);

        // Prepare data
        const chartData = this.protocols.map(protocol => {
            const result = this.results.get(protocol.id);
            return {
                name: protocol.name,
                color: protocol.color,
                duration: result ? result.duration : 0,
                success: result ? result.success : false
            };
        });

        // Scales
        const xScale = d3.scaleBand()
            .domain(chartData.map(d => d.name))
            .range([0, width])
            .padding(0.2);

        const yMax = d3.max(chartData, d => d.duration) * 1.2;
        const yScale = d3.scaleLinear()
            .domain([0, yMax])
            .range([height, 0]);

        // Axes
        g.append('g')
            .attr('class', 'axis x-axis')
            .attr('transform', `translate(0,${height})`)
            .call(d3.axisBottom(xScale))
            .append('text')
            .attr('class', 'axis-label')
            .attr('x', width / 2)
            .attr('y', 45)
            .attr('fill', '#8b949e')
            .style('text-anchor', 'middle')
            .text('Protocol');

        g.append('g')
            .attr('class', 'axis y-axis')
            .call(d3.axisLeft(yScale))
            .append('text')
            .attr('class', 'axis-label')
            .attr('transform', 'rotate(-90)')
            .attr('x', -height / 2)
            .attr('y', -50)
            .attr('fill', '#8b949e')
            .style('text-anchor', 'middle')
            .text('Time to Load (ms)');

        // Bars
        g.selectAll('.bar')
            .data(chartData)
            .enter()
            .append('rect')
            .attr('class', d => `bar ${d.success ? 'success' : 'failure'}`)
            .attr('x', d => xScale(d.name))
            .attr('y', d => yScale(d.duration))
            .attr('width', xScale.bandwidth())
            .attr('height', d => height - yScale(d.duration))
            .attr('fill', d => d.color)
            .attr('opacity', d => d.success ? 0.9 : 0.3);

        // Labels
        g.selectAll('.bar-label')
            .data(chartData)
            .enter()
            .append('text')
            .attr('class', 'bar-label')
            .attr('x', d => xScale(d.name) + xScale.bandwidth() / 2)
            .attr('y', d => yScale(d.duration) - 5)
            .attr('text-anchor', 'middle')
            .attr('fill', '#f0f6fc')
            .attr('font-size', '12px')
            .text(d => d.success ? `${d.duration.toFixed(0)}ms` : 'Failed');

        // Title
        svg.append('text')
            .attr('class', 'chart-title')
            .attr('x', (width + margin.left + margin.right) / 2)
            .attr('y', 20)
            .attr('text-anchor', 'middle')
            .attr('fill', '#f0f6fc')
            .attr('font-size', '16px')
            .attr('font-weight', 'bold')
            .text('Image Loading Performance Comparison');
    }
}

/**
 * Initialize the image loading test when DOM is ready
 */
export function initImageLoadingTest() {
    const test = new ImageLoadingTest('image-loading-test-container');
    test.init();
    return test;
}
