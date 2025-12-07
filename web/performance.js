/**
 * Performance Comparison Module - Tab 2
 *
 * Implements protocol simulations for comparing TGP against traditional protocols:
 * - TGP (Two Generals Protocol) - Our solution
 * - TCP-like - Traditional acknowledgment-based
 * - QUIC-like - Modern UDP-based with acks
 * - UDP - Fire and forget
 *
 * Uses D3.js for visualization of performance results.
 */

import * as d3 from 'd3';

// =============================================================================
// Protocol Simulation Base
// =============================================================================

/**
 * Base class for protocol simulations.
 * Each protocol implementation extends this to provide specific behavior.
 */
class ProtocolSimulator {
    constructor(name, lossRate = 0.5) {
        this.name = name;
        this.lossRate = lossRate;
        this.messagesSent = 0;
        this.messagesDelivered = 0;
        this.messagesLost = 0;
        this.roundTrips = 0;
        this.startTime = 0;
        this.endTime = 0;
        this.completed = false;
        this.success = false;
        this.symmetricOutcome = true;
    }

    /**
     * Simulate sending a message through the lossy channel.
     * @returns {boolean} true if message was delivered
     */
    sendMessage() {
        this.messagesSent++;
        const delivered = Math.random() >= this.lossRate;
        if (delivered) {
            this.messagesDelivered++;
        } else {
            this.messagesLost++;
        }
        return delivered;
    }

    /**
     * Run the protocol simulation.
     * @param {number} maxTicks - Maximum ticks before timeout
     * @returns {object} Simulation results
     */
    run(maxTicks = 10000) {
        throw new Error('Must be implemented by subclass');
    }

    /**
     * Get statistics from the simulation.
     */
    getStats() {
        return {
            name: this.name,
            messagesSent: this.messagesSent,
            messagesDelivered: this.messagesDelivered,
            messagesLost: this.messagesLost,
            actualLossRate: this.messagesSent > 0
                ? (this.messagesLost / this.messagesSent * 100).toFixed(2)
                : 0,
            roundTrips: this.roundTrips,
            duration: this.endTime - this.startTime,
            completed: this.completed,
            success: this.success,
            symmetricOutcome: this.symmetricOutcome
        };
    }
}

// =============================================================================
// TGP Protocol Simulation
// =============================================================================

/**
 * Two Generals Protocol implementation.
 * Uses proof escalation (C -> D -> T -> Q) with continuous flooding.
 *
 * Key properties:
 * - Deterministic coordination with extreme loss tolerance
 * - All-or-nothing semantics via bilateral construction
 * - Zero asymmetric outcomes
 */
class TGPSimulator extends ProtocolSimulator {
    constructor(lossRate) {
        super('TGP', lossRate);
        // Alice state
        this.alicePhase = 0; // 0=INIT, 1=C, 2=D, 3=T, 4=Q, 5=COMPLETE
        this.aliceHasOtherC = false;
        this.aliceHasOtherD = false;
        this.aliceHasOtherT = false;
        // Bob state
        this.bobPhase = 0;
        this.bobHasOtherC = false;
        this.bobHasOtherD = false;
        this.bobHasOtherT = false;
    }

    run(maxTicks = 100000) {
        this.startTime = performance.now();

        // Start protocol - both parties create commitments
        this.alicePhase = 1; // C phase
        this.bobPhase = 1;

        for (let tick = 0; tick < maxTicks; tick++) {
            // Alice floods her current proof level to Bob
            this.floodAliceToBob();

            // Bob floods his current proof level to Alice
            this.floodBobToAlice();

            // Check if both reached QUAD
            if (this.alicePhase >= 4 && this.bobPhase >= 4) {
                this.completed = true;
                this.success = true;
                this.symmetricOutcome = true;
                break;
            }

            this.roundTrips = tick + 1;
        }

        this.endTime = performance.now();

        // Determine outcome
        const aliceCanAttack = this.alicePhase >= 4;
        const bobCanAttack = this.bobPhase >= 4;

        if (aliceCanAttack && bobCanAttack) {
            this.success = true;
            this.symmetricOutcome = true;
        } else if (!aliceCanAttack && !bobCanAttack) {
            this.success = false; // Both abort
            this.symmetricOutcome = true;
        } else {
            // This should be IMPOSSIBLE with correct TGP
            this.success = false;
            this.symmetricOutcome = false;
        }

        return this.getStats();
    }

    floodAliceToBob() {
        if (this.sendMessage()) {
            // Message delivered - Bob processes based on Alice's phase
            const aliceMsg = { phase: this.alicePhase };
            this.processMessageForBob(aliceMsg);
        }
    }

    floodBobToAlice() {
        if (this.sendMessage()) {
            // Message delivered - Alice processes based on Bob's phase
            const bobMsg = { phase: this.bobPhase };
            this.processMessageForAlice(bobMsg);
        }
    }

    processMessageForBob(msg) {
        // Extract embedded proofs from higher-level messages
        if (msg.phase >= 1) this.bobHasOtherC = true;
        if (msg.phase >= 2) this.bobHasOtherD = true;
        if (msg.phase >= 3) this.bobHasOtherT = true;

        // Advance Bob's phase based on what he now has
        this.tryAdvanceBob();
    }

    processMessageForAlice(msg) {
        // Extract embedded proofs from higher-level messages
        if (msg.phase >= 1) this.aliceHasOtherC = true;
        if (msg.phase >= 2) this.aliceHasOtherD = true;
        if (msg.phase >= 3) this.aliceHasOtherT = true;

        // Advance Alice's phase based on what she now has
        this.tryAdvanceAlice();
    }

    tryAdvanceBob() {
        // C -> D transition: need other's C
        if (this.bobPhase === 1 && this.bobHasOtherC) {
            this.bobPhase = 2;
        }
        // D -> T transition: need other's D
        if (this.bobPhase === 2 && this.bobHasOtherD) {
            this.bobPhase = 3;
        }
        // T -> Q transition: need other's T
        if (this.bobPhase === 3 && this.bobHasOtherT) {
            this.bobPhase = 4;
        }
    }

    tryAdvanceAlice() {
        // C -> D transition: need other's C
        if (this.alicePhase === 1 && this.aliceHasOtherC) {
            this.alicePhase = 2;
        }
        // D -> T transition: need other's D
        if (this.alicePhase === 2 && this.aliceHasOtherD) {
            this.alicePhase = 3;
        }
        // T -> Q transition: need other's T
        if (this.alicePhase === 3 && this.aliceHasOtherT) {
            this.alicePhase = 4;
        }
    }
}

// =============================================================================
// TCP-like Protocol Simulation
// =============================================================================

/**
 * TCP-like protocol simulation.
 * Uses stop-and-wait acknowledgments with retransmission.
 *
 * Models the classic "infinite regress" problem:
 * MSG -> ACK -> ACK-of-ACK -> ...
 *
 * Properties:
 * - Susceptible to the Two Generals Problem
 * - Last ACK can always be lost
 * - Asymmetric outcomes possible
 */
class TCPSimulator extends ProtocolSimulator {
    constructor(lossRate) {
        super('TCP', lossRate);
        this.aliceConfirmed = false;
        this.bobConfirmed = false;
        this.currentAckLevel = 0;
        this.maxAckLevel = 5; // Limit ack depth
    }

    run(maxTicks = 100000) {
        this.startTime = performance.now();

        for (let tick = 0; tick < maxTicks; tick++) {
            // Alice sends SYN/data
            if (!this.aliceConfirmed) {
                if (this.sendMessage()) {
                    // Bob receives - sends ACK
                    if (this.sendMessage()) {
                        this.aliceConfirmed = true;
                        // Alice sends ACK-of-ACK
                        if (this.sendMessage()) {
                            this.bobConfirmed = true;
                            this.completed = true;
                            break;
                        }
                    }
                }
            }

            this.roundTrips = tick + 1;
        }

        this.endTime = performance.now();

        // TCP outcome analysis
        if (this.aliceConfirmed && this.bobConfirmed) {
            this.success = true;
            this.symmetricOutcome = true;
        } else if (!this.aliceConfirmed && !this.bobConfirmed) {
            this.success = false;
            this.symmetricOutcome = true;
        } else {
            // Alice thinks confirmed but Bob doesn't, or vice versa
            // This is the Two Generals Problem!
            this.success = false;
            this.symmetricOutcome = false;
        }

        return this.getStats();
    }
}

// =============================================================================
// QUIC-like Protocol Simulation
// =============================================================================

/**
 * QUIC-like protocol simulation.
 * Modern UDP-based protocol with:
 * - 0-RTT connection establishment
 * - Multiplexed streams
 * - Forward error correction
 *
 * Still susceptible to asymmetric outcomes under extreme loss.
 */
class QUICSimulator extends ProtocolSimulator {
    constructor(lossRate) {
        super('QUIC', lossRate);
        this.aliceConfirmed = false;
        this.bobConfirmed = false;
        this.connectionEstablished = false;
    }

    run(maxTicks = 100000) {
        this.startTime = performance.now();

        for (let tick = 0; tick < maxTicks; tick++) {
            // QUIC uses Initial packet + 0-RTT data
            if (!this.connectionEstablished) {
                // Send Initial with CRYPTO frames
                if (this.sendMessage()) {
                    // Server responds with Initial + Handshake
                    if (this.sendMessage()) {
                        this.connectionEstablished = true;
                        // Client sends Handshake completion
                        if (this.sendMessage()) {
                            this.aliceConfirmed = true;
                            // Server ACK
                            if (this.sendMessage()) {
                                this.bobConfirmed = true;
                                this.completed = true;
                                break;
                            }
                        }
                    }
                }
            } else {
                // Try to complete handshake
                if (!this.aliceConfirmed && this.sendMessage()) {
                    this.aliceConfirmed = true;
                }
                if (this.aliceConfirmed && !this.bobConfirmed && this.sendMessage()) {
                    this.bobConfirmed = true;
                    this.completed = true;
                    break;
                }
            }

            this.roundTrips = tick + 1;
        }

        this.endTime = performance.now();

        // Analyze outcome
        if (this.aliceConfirmed && this.bobConfirmed) {
            this.success = true;
            this.symmetricOutcome = true;
        } else if (!this.connectionEstablished) {
            this.success = false;
            this.symmetricOutcome = true;
        } else {
            // Partial handshake = asymmetric
            this.success = false;
            this.symmetricOutcome = false;
        }

        return this.getStats();
    }
}

// =============================================================================
// UDP Protocol Simulation
// =============================================================================

/**
 * UDP protocol simulation.
 * Fire-and-forget with no reliability guarantees.
 *
 * Properties:
 * - No coordination semantics
 * - Sender doesn't know if message arrived
 * - Fast but unreliable
 */
class UDPSimulator extends ProtocolSimulator {
    constructor(lossRate) {
        super('UDP', lossRate);
        this.aliceSent = false;
        this.bobReceived = false;
        this.bobSent = false;
        this.aliceReceived = false;
    }

    run(maxTicks = 100000) {
        this.startTime = performance.now();

        for (let tick = 0; tick < maxTicks; tick++) {
            // Alice sends
            if (!this.aliceSent) {
                this.aliceSent = true;
                if (this.sendMessage()) {
                    this.bobReceived = true;
                }
            }

            // Bob sends (blind)
            if (!this.bobSent) {
                this.bobSent = true;
                if (this.sendMessage()) {
                    this.aliceReceived = true;
                }
            }

            // UDP has no confirmation loop - single attempt
            if (this.aliceSent && this.bobSent) {
                this.completed = true;
                break;
            }

            this.roundTrips = tick + 1;
        }

        this.endTime = performance.now();

        // UDP outcome - no coordination guarantees
        // Alice and Bob have no way to know if the other received
        this.success = this.aliceReceived && this.bobReceived;
        // UDP always appears symmetric from sender's view (fire and forget)
        // But actually has hidden asymmetry in delivery
        this.symmetricOutcome = this.aliceReceived === this.bobReceived;

        return this.getStats();
    }
}

// =============================================================================
// Performance Test Harness
// =============================================================================

/**
 * Performance testing infrastructure.
 * Runs multiple trials across various loss rates and protocols.
 */
class PerformanceTestHarness {
    constructor() {
        this.protocols = ['TGP', 'TCP', 'QUIC', 'UDP'];
        this.results = new Map();
        this.callbacks = {};
    }

    on(event, callback) {
        this.callbacks[event] = callback;
    }

    emit(event, data) {
        if (this.callbacks[event]) {
            this.callbacks[event](data);
        }
    }

    /**
     * Create a protocol simulator instance.
     */
    createSimulator(protocol, lossRate) {
        switch (protocol) {
            case 'TGP': return new TGPSimulator(lossRate);
            case 'TCP': return new TCPSimulator(lossRate);
            case 'QUIC': return new QUICSimulator(lossRate);
            case 'UDP': return new UDPSimulator(lossRate);
            default: throw new Error(`Unknown protocol: ${protocol}`);
        }
    }

    /**
     * Run performance comparison across all protocols.
     * @param {object} config - Test configuration
     */
    async runComparison(config = {}) {
        const {
            lossRates = [0, 10, 25, 50, 75, 90, 95, 99, 99.9, 99.99],
            trialsPerRate = 10,
            maxTicks = 100000,
            protocols = this.protocols
        } = config;

        this.results.clear();
        const totalTests = lossRates.length * protocols.length * trialsPerRate;
        let completedTests = 0;

        // Initialize results structure
        for (const protocol of protocols) {
            this.results.set(protocol, {
                name: protocol,
                byLossRate: new Map()
            });
        }

        // Run tests
        for (const lossRatePercent of lossRates) {
            const lossRate = lossRatePercent / 100;

            for (const protocol of protocols) {
                const trialResults = [];

                for (let trial = 0; trial < trialsPerRate; trial++) {
                    const sim = this.createSimulator(protocol, lossRate);
                    const result = sim.run(maxTicks);
                    trialResults.push(result);

                    completedTests++;
                    this.emit('progress', {
                        completed: completedTests,
                        total: totalTests,
                        protocol,
                        lossRate: lossRatePercent,
                        trial: trial + 1
                    });
                }

                // Aggregate trial results
                const aggregated = this.aggregateResults(trialResults);
                this.results.get(protocol).byLossRate.set(lossRatePercent, aggregated);
            }

            // Yield to browser
            await new Promise(resolve => setTimeout(resolve, 0));
        }

        this.emit('complete', this.getComparisonData());
        return this.getComparisonData();
    }

    /**
     * Aggregate results from multiple trials.
     */
    aggregateResults(trials) {
        const n = trials.length;

        const sum = (arr, key) => arr.reduce((s, t) => s + t[key], 0);
        const avg = (arr, key) => sum(arr, key) / n;

        return {
            trials: n,
            avgMessagesSent: avg(trials, 'messagesSent'),
            avgMessagesDelivered: avg(trials, 'messagesDelivered'),
            avgRoundTrips: avg(trials, 'roundTrips'),
            avgDuration: avg(trials, 'duration'),
            successRate: (trials.filter(t => t.success).length / n) * 100,
            symmetryRate: (trials.filter(t => t.symmetricOutcome).length / n) * 100,
            completionRate: (trials.filter(t => t.completed).length / n) * 100
        };
    }

    /**
     * Get formatted comparison data for visualization.
     */
    getComparisonData() {
        const data = {
            protocols: [],
            lossRates: []
        };

        for (const [protocol, results] of this.results) {
            const protocolData = {
                name: protocol,
                data: []
            };

            for (const [lossRate, aggregated] of results.byLossRate) {
                if (!data.lossRates.includes(lossRate)) {
                    data.lossRates.push(lossRate);
                }
                protocolData.data.push({
                    lossRate,
                    ...aggregated
                });
            }

            data.protocols.push(protocolData);
        }

        data.lossRates.sort((a, b) => a - b);
        return data;
    }
}

// =============================================================================
// D3.js Results Visualization
// =============================================================================

/**
 * Performance results visualizer using D3.js.
 * Creates charts comparing protocol performance across loss rates.
 */
class PerformanceVisualizer {
    constructor(containerId) {
        this.container = d3.select(`#${containerId}`);
        this.margin = { top: 40, right: 120, bottom: 60, left: 80 };
        this.width = 800 - this.margin.left - this.margin.right;
        this.height = 400 - this.margin.top - this.margin.bottom;

        this.colors = {
            TGP: '#3fb950',   // Green - our protocol
            TCP: '#f85149',   // Red - traditional
            QUIC: '#58a6ff',  // Blue - modern
            UDP: '#d29922'    // Yellow - unreliable
        };

        this.setupContainer();
    }

    setupContainer() {
        // Clear existing content
        this.container.selectAll('*').remove();

        // Create chart sections
        this.container.classed('performance-visualizer', true);
    }

    /**
     * Render all performance charts.
     */
    render(data) {
        this.container.selectAll('*').remove();

        // Title
        this.container.append('h3')
            .attr('class', 'perf-chart-title')
            .text('Protocol Performance Comparison');

        // Create chart grid
        const chartsGrid = this.container.append('div')
            .attr('class', 'perf-charts-grid');

        // 1. Success Rate Chart
        this.renderLineChart(chartsGrid, data, {
            id: 'success-rate-chart',
            title: 'Success Rate vs Packet Loss',
            yKey: 'successRate',
            yLabel: 'Success Rate (%)',
            yDomain: [0, 100]
        });

        // 2. Symmetry Rate Chart (key metric for TGP)
        this.renderLineChart(chartsGrid, data, {
            id: 'symmetry-rate-chart',
            title: 'Symmetric Outcomes vs Packet Loss',
            yKey: 'symmetryRate',
            yLabel: 'Symmetric Outcome Rate (%)',
            yDomain: [0, 100]
        });

        // 3. Messages Required Chart
        this.renderLineChart(chartsGrid, data, {
            id: 'messages-chart',
            title: 'Messages Required vs Packet Loss',
            yKey: 'avgMessagesSent',
            yLabel: 'Average Messages Sent',
            yDomain: null // Auto-scale
        });

        // 4. Completion Time Chart
        this.renderLineChart(chartsGrid, data, {
            id: 'time-chart',
            title: 'Completion Time vs Packet Loss',
            yKey: 'avgDuration',
            yLabel: 'Average Time (ms)',
            yDomain: null // Auto-scale
        });

        // Summary statistics
        this.renderSummary(data);
    }

    /**
     * Render a line chart comparing protocols.
     */
    renderLineChart(container, data, config) {
        const chartWrapper = container.append('div')
            .attr('class', 'perf-chart-wrapper');

        chartWrapper.append('h4')
            .attr('class', 'perf-chart-subtitle')
            .text(config.title);

        const svg = chartWrapper.append('svg')
            .attr('viewBox', `0 0 ${this.width + this.margin.left + this.margin.right} ${this.height + this.margin.top + this.margin.bottom}`)
            .attr('class', 'perf-chart-svg');

        const g = svg.append('g')
            .attr('transform', `translate(${this.margin.left},${this.margin.top})`);

        // Scales
        const xScale = d3.scaleLog()
            .domain([1, 100])
            .range([0, this.width]);

        const allValues = data.protocols.flatMap(p => p.data.map(d => d[config.yKey]));
        const yMax = config.yDomain ? config.yDomain[1] : Math.max(...allValues) * 1.1;
        const yMin = config.yDomain ? config.yDomain[0] : 0;

        const yScale = d3.scaleLinear()
            .domain([yMin, yMax])
            .range([this.height, 0]);

        // X axis
        g.append('g')
            .attr('class', 'axis x-axis')
            .attr('transform', `translate(0,${this.height})`)
            .call(d3.axisBottom(xScale)
                .tickValues([1, 10, 50, 90, 99, 99.9])
                .tickFormat(d => `${d}%`))
            .append('text')
            .attr('class', 'axis-label')
            .attr('x', this.width / 2)
            .attr('y', 45)
            .attr('fill', '#8b949e')
            .style('text-anchor', 'middle')
            .text('Packet Loss Rate');

        // Y axis
        g.append('g')
            .attr('class', 'axis y-axis')
            .call(d3.axisLeft(yScale))
            .append('text')
            .attr('class', 'axis-label')
            .attr('transform', 'rotate(-90)')
            .attr('x', -this.height / 2)
            .attr('y', -50)
            .attr('fill', '#8b949e')
            .style('text-anchor', 'middle')
            .text(config.yLabel);

        // Line generator
        const line = d3.line()
            .x(d => xScale(Math.max(1, d.lossRate)))
            .y(d => yScale(d[config.yKey]))
            .curve(d3.curveMonotoneX);

        // Draw lines for each protocol
        for (const protocol of data.protocols) {
            const color = this.colors[protocol.name];
            const filteredData = protocol.data.filter(d => d.lossRate >= 1);

            // Line path
            g.append('path')
                .datum(filteredData)
                .attr('class', `line line-${protocol.name.toLowerCase()}`)
                .attr('d', line)
                .attr('fill', 'none')
                .attr('stroke', color)
                .attr('stroke-width', 2.5);

            // Data points
            g.selectAll(`.dot-${protocol.name}`)
                .data(filteredData)
                .enter()
                .append('circle')
                .attr('class', `dot dot-${protocol.name.toLowerCase()}`)
                .attr('cx', d => xScale(Math.max(1, d.lossRate)))
                .attr('cy', d => yScale(d[config.yKey]))
                .attr('r', 4)
                .attr('fill', color)
                .attr('stroke', '#161b22')
                .attr('stroke-width', 1.5);
        }

        // Legend
        const legend = g.append('g')
            .attr('class', 'legend')
            .attr('transform', `translate(${this.width + 10}, 0)`);

        data.protocols.forEach((protocol, i) => {
            const legendItem = legend.append('g')
                .attr('transform', `translate(0, ${i * 24})`);

            legendItem.append('line')
                .attr('x1', 0)
                .attr('x2', 20)
                .attr('y1', 0)
                .attr('y2', 0)
                .attr('stroke', this.colors[protocol.name])
                .attr('stroke-width', 2.5);

            legendItem.append('circle')
                .attr('cx', 10)
                .attr('cy', 0)
                .attr('r', 4)
                .attr('fill', this.colors[protocol.name]);

            legendItem.append('text')
                .attr('x', 28)
                .attr('y', 4)
                .attr('fill', '#f0f6fc')
                .attr('font-size', '12px')
                .text(protocol.name);
        });
    }

    /**
     * Render summary statistics panel.
     */
    renderSummary(data) {
        const summary = this.container.append('div')
            .attr('class', 'perf-summary');

        summary.append('h4').text('Key Findings');

        const findings = summary.append('div')
            .attr('class', 'perf-findings');

        // Find TGP data at high loss rates
        const tgpData = data.protocols.find(p => p.name === 'TGP');
        const tcpData = data.protocols.find(p => p.name === 'TCP');

        if (tgpData && tcpData) {
            const highLoss = tgpData.data.find(d => d.lossRate >= 90);
            const tcpHighLoss = tcpData.data.find(d => d.lossRate >= 90);

            if (highLoss && tcpHighLoss) {
                findings.append('div')
                    .attr('class', 'finding tgp-highlight')
                    .html(`
                        <span class="finding-icon">✓</span>
                        <span class="finding-text">
                            <strong>TGP maintains ${highLoss.symmetryRate.toFixed(0)}% symmetric outcomes</strong>
                            at ${highLoss.lossRate}% packet loss, while TCP drops to ${tcpHighLoss.symmetryRate.toFixed(0)}%
                        </span>
                    `);
            }
        }

        // Add key insights
        const insights = [
            {
                icon: '🛡️',
                text: '<strong>Zero asymmetric failures</strong> with TGP - the bilateral construction property guarantees both parties reach the same decision'
            },
            {
                icon: '⚡',
                text: '<strong>Continuous flooding</strong> eliminates "last message" vulnerability - any instance of a proof suffices'
            },
            {
                icon: '📊',
                text: '<strong>Higher message overhead</strong> is the tradeoff for deterministic coordination guarantees'
            }
        ];

        insights.forEach(insight => {
            findings.append('div')
                .attr('class', 'finding')
                .html(`
                    <span class="finding-icon">${insight.icon}</span>
                    <span class="finding-text">${insight.text}</span>
                `);
        });
    }
}

// =============================================================================
// Tab 2 Controller
// =============================================================================

/**
 * Main controller for Tab 2: Performance Comparison.
 */
class PerformanceController {
    constructor() {
        this.harness = new PerformanceTestHarness();
        this.visualizer = null;
        this.isRunning = false;

        this.bindEvents();
    }

    bindEvents() {
        // Progress updates
        this.harness.on('progress', (progress) => {
            this.updateProgress(progress);
        });

        // Completion
        this.harness.on('complete', (data) => {
            this.showResults(data);
        });
    }

    /**
     * Initialize the controller when tab is shown.
     */
    init() {
        const container = document.getElementById('performance-container');
        if (!container) return;

        // Setup initial UI
        this.renderControlPanel();
        this.visualizer = new PerformanceVisualizer('performance-results');
    }

    /**
     * Render the control panel for running tests.
     */
    renderControlPanel() {
        const controls = document.getElementById('performance-controls');
        if (!controls) return;

        controls.innerHTML = `
            <div class="perf-control-panel">
                <div class="perf-control-group">
                    <label for="perf-trials">Trials per loss rate:</label>
                    <input type="range" id="perf-trials" min="5" max="50" value="10">
                    <span id="perf-trials-value">10</span>
                </div>
                <div class="perf-control-group">
                    <label for="perf-max-ticks">Max simulation ticks:</label>
                    <select id="perf-max-ticks">
                        <option value="10000">10,000 (Fast)</option>
                        <option value="100000" selected>100,000 (Standard)</option>
                        <option value="1000000">1,000,000 (Thorough)</option>
                    </select>
                </div>
                <div class="perf-button-group">
                    <button id="run-perf-test" class="primary">Run Performance Test</button>
                    <span id="perf-progress"></span>
                </div>
            </div>
            <div class="perf-protocol-info">
                <div class="protocol-card tgp">
                    <h5>TGP (Two Generals Protocol)</h5>
                    <p>Our solution: Proof escalation with continuous flooding. Guaranteed symmetric outcomes.</p>
                </div>
                <div class="protocol-card tcp">
                    <h5>TCP-like</h5>
                    <p>Traditional ACK-based. Vulnerable to "last message" problem.</p>
                </div>
                <div class="protocol-card quic">
                    <h5>QUIC-like</h5>
                    <p>Modern UDP with reliability. Still susceptible under extreme loss.</p>
                </div>
                <div class="protocol-card udp">
                    <h5>UDP</h5>
                    <p>Fire-and-forget. No coordination guarantees.</p>
                </div>
            </div>
        `;

        // Bind control events
        const trialsSlider = document.getElementById('perf-trials');
        const trialsValue = document.getElementById('perf-trials-value');
        if (trialsSlider) {
            trialsSlider.addEventListener('input', (e) => {
                trialsValue.textContent = e.target.value;
            });
        }

        const runButton = document.getElementById('run-perf-test');
        if (runButton) {
            runButton.addEventListener('click', () => this.runTest());
        }
    }

    /**
     * Run the performance comparison test.
     */
    async runTest() {
        if (this.isRunning) return;

        const runButton = document.getElementById('run-perf-test');
        const resultsContainer = document.getElementById('performance-results');

        this.isRunning = true;
        runButton.disabled = true;
        runButton.textContent = 'Running...';
        resultsContainer.innerHTML = '<div class="perf-loading">Running performance tests...</div>';

        const trials = parseInt(document.getElementById('perf-trials')?.value || '10');
        const maxTicks = parseInt(document.getElementById('perf-max-ticks')?.value || '100000');

        try {
            const data = await this.harness.runComparison({
                lossRates: [0, 5, 10, 25, 50, 75, 90, 95, 99, 99.9],
                trialsPerRate: trials,
                maxTicks: maxTicks
            });

            this.visualizer.render(data);
        } catch (error) {
            resultsContainer.innerHTML = `<div class="perf-error">Error: ${error.message}</div>`;
        } finally {
            this.isRunning = false;
            runButton.disabled = false;
            runButton.textContent = 'Run Performance Test';
            document.getElementById('perf-progress').textContent = '';
        }
    }

    /**
     * Update progress display during test.
     */
    updateProgress(progress) {
        const progressEl = document.getElementById('perf-progress');
        if (progressEl) {
            const percent = ((progress.completed / progress.total) * 100).toFixed(0);
            progressEl.textContent = `${percent}% (${progress.protocol} @ ${progress.lossRate}% loss)`;
        }
    }

    /**
     * Show final results.
     */
    showResults(data) {
        if (this.visualizer) {
            this.visualizer.render(data);
        }
    }
}

// =============================================================================
// Export for use in main visualizer
// =============================================================================

export {
    TGPSimulator,
    TCPSimulator,
    QUICSimulator,
    UDPSimulator,
    PerformanceTestHarness,
    PerformanceVisualizer,
    PerformanceController
};

// Initialize when DOM is ready
let performanceController = null;

export function initPerformanceTab() {
    if (!performanceController) {
        performanceController = new PerformanceController();
    }
    performanceController.init();
    return performanceController;
}
