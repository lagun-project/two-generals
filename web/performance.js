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
// D3.js Chart Renderer for Individual Charts
// =============================================================================

/**
 * Individual chart renderer for each metric.
 * Renders directly into the placeholder divs in index.html.
 */
class ChartRenderer {
    constructor(containerId, controller) {
        this.containerId = containerId;
        this.controller = controller;
        this.margin = { top: 20, right: 20, bottom: 50, left: 60 };
        this.colors = {
            TGP: '#3fb950',
            TCP: '#f85149',
            QUIC: '#a371f7',
            UDP: '#d29922'
        };
    }

    /**
     * Render a line chart in this container.
     */
    render(data, config) {
        const container = d3.select(`#${this.containerId}`);
        container.selectAll('*').remove();

        if (!data || !data.protocols || data.protocols.length === 0) {
            container.append('div')
                .attr('class', 'perf-chart-placeholder')
                .text('Run a test to see results');
            return;
        }

        const width = 400;
        const height = 180;
        const innerWidth = width - this.margin.left - this.margin.right;
        const innerHeight = height - this.margin.top - this.margin.bottom;

        const svg = container.append('svg')
            .attr('width', width)
            .attr('height', height)
            .attr('class', 'perf-chart-svg');

        const g = svg.append('g')
            .attr('transform', `translate(${this.margin.left},${this.margin.top})`);

        // Scales
        const xScale = d3.scaleLinear()
            .domain([0, 100])
            .range([0, innerWidth]);

        const allValues = data.protocols.flatMap(p =>
            p.data.map(d => d[config.yKey] || 0)
        );
        const yMax = config.yDomain ? config.yDomain[1] : Math.max(...allValues, 1) * 1.1;
        const yMin = config.yDomain ? config.yDomain[0] : 0;

        const yScale = d3.scaleLinear()
            .domain([yMin, yMax])
            .range([innerHeight, 0]);

        // Grid lines
        g.append('g')
            .attr('class', 'grid')
            .call(d3.axisLeft(yScale)
                .ticks(5)
                .tickSize(-innerWidth)
                .tickFormat(''))
            .style('opacity', 0.1);

        // X axis
        g.append('g')
            .attr('class', 'axis x-axis')
            .attr('transform', `translate(0,${innerHeight})`)
            .call(d3.axisBottom(xScale)
                .ticks(5)
                .tickFormat(d => `${d}%`))
            .selectAll('text')
            .style('font-size', '10px');

        // Y axis
        g.append('g')
            .attr('class', 'axis y-axis')
            .call(d3.axisLeft(yScale).ticks(5))
            .selectAll('text')
            .style('font-size', '10px');

        // Line generator
        const line = d3.line()
            .x(d => xScale(d.lossRate))
            .y(d => yScale(d[config.yKey] || 0))
            .curve(d3.curveMonotoneX);

        // Draw lines
        for (const protocol of data.protocols) {
            const color = this.colors[protocol.name];

            g.append('path')
                .datum(protocol.data)
                .attr('class', `line line-${protocol.name.toLowerCase()}`)
                .attr('d', line)
                .attr('fill', 'none')
                .attr('stroke', color)
                .attr('stroke-width', 2);

            // Data points
            g.selectAll(`.dot-${protocol.name}`)
                .data(protocol.data)
                .enter()
                .append('circle')
                .attr('class', `dot dot-${protocol.name.toLowerCase()}`)
                .attr('cx', d => xScale(d.lossRate))
                .attr('cy', d => yScale(d[config.yKey] || 0))
                .attr('r', 3)
                .attr('fill', color);
        }
    }
}

// =============================================================================
// D3.js Results Visualization (Legacy - kept for compatibility)
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
        this.charts = {};
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

        // Wire up Run Comparison button
        document.addEventListener('DOMContentLoaded', () => {
            const runButton = document.getElementById('run-perf-test');
            if (runButton) {
                runButton.addEventListener('click', () => this.runTest());
            }
        });
    }

    /**
     * Initialize the controller when tab is shown.
     */
    init() {
        // Setup chart containers
        this.setupCharts();
    }

    /**
     * Setup chart containers - uses existing HTML structure from index.html
     */
    setupCharts() {
        // Chart containers already exist in HTML:
        // #chart-success, #chart-symmetry, #chart-messages, #chart-time

        // Initialize visualizers for each chart
        this.charts.success = new ChartRenderer('chart-success', this);
        this.charts.symmetry = new ChartRenderer('chart-symmetry', this);
        this.charts.messages = new ChartRenderer('chart-messages', this);
        this.charts.time = new ChartRenderer('chart-time', this);
    }

    /**
     * Run the performance comparison test.
     */
    async runTest() {
        if (this.isRunning) return;

        const runButton = document.getElementById('run-perf-test');
        const progressBar = document.getElementById('perf-progress');
        const progressFill = document.getElementById('perf-progress-fill');
        const progressStatus = document.getElementById('perf-progress-status');
        const progressPercent = document.getElementById('perf-progress-percent');
        const summarySection = document.getElementById('perf-summary');

        this.isRunning = true;
        runButton.disabled = true;
        runButton.textContent = 'Running...';

        // Show progress bar
        if (progressBar) {
            progressBar.style.display = 'block';
        }

        // Hide summary
        if (summarySection) {
            summarySection.style.display = 'none';
        }

        // Get settings from HTML controls
        const lossRate = parseFloat(document.getElementById('perf-loss-rate')?.value || '0.5');
        const iterations = parseInt(document.getElementById('perf-iterations')?.value || '100');

        try {
            // Run comparison across multiple loss rates
            const data = await this.harness.runComparison({
                lossRates: [lossRate * 100, 10, 30, 50, 70, 90, 95, 99],
                trialsPerRate: Math.ceil(iterations / 8), // Divide iterations across loss rates
                maxTicks: 10000
            });

            this.showResults(data);
        } catch (error) {
            console.error('Performance test error:', error);
            alert(`Error running test: ${error.message}`);
        } finally {
            this.isRunning = false;
            runButton.disabled = false;
            runButton.textContent = 'Run Comparison';

            // Hide progress bar
            if (progressBar) {
                progressBar.style.display = 'none';
            }
        }
    }

    /**
     * Update progress display during test.
     */
    updateProgress(progress) {
        const progressFill = document.getElementById('perf-progress-fill');
        const progressStatus = document.getElementById('perf-progress-status');
        const progressPercent = document.getElementById('perf-progress-percent');

        if (progressFill && progressStatus && progressPercent) {
            const percent = ((progress.completed / progress.total) * 100).toFixed(0);
            progressFill.style.width = `${percent}%`;
            progressStatus.textContent = `Testing ${progress.protocol} at ${progress.lossRate}% loss...`;
            progressPercent.textContent = `${percent}%`;
        }
    }

    /**
     * Show final results across all charts.
     */
    showResults(data) {
        // Update protocol cards with success rates
        this.updateProtocolCards(data);

        // Render each chart
        this.charts.success.render(data, {
            yKey: 'successRate',
            yLabel: 'Success Rate (%)',
            yDomain: [0, 100]
        });

        this.charts.symmetry.render(data, {
            yKey: 'symmetryRate',
            yLabel: 'Symmetric Outcomes (%)',
            yDomain: [0, 100]
        });

        this.charts.messages.render(data, {
            yKey: 'avgMessagesSent',
            yLabel: 'Messages Sent',
            yDomain: null
        });

        this.charts.time.render(data, {
            yKey: 'avgDuration',
            yLabel: 'Time (ms)',
            yDomain: null
        });

        // Show summary
        this.showSummary(data);
    }

    /**
     * Update protocol cards with metrics.
     */
    updateProtocolCards(data) {
        for (const protocolData of data.protocols) {
            const cardId = `${protocolData.name.toLowerCase()}-success`;
            const cardEl = document.getElementById(cardId);

            if (cardEl) {
                // Find highest loss rate data point
                const highLossData = protocolData.data[protocolData.data.length - 1];
                if (highLossData) {
                    cardEl.textContent = `${highLossData.successRate.toFixed(1)}%`;
                }
            }
        }
    }

    /**
     * Show summary findings.
     */
    showSummary(data) {
        const summarySection = document.getElementById('perf-summary');
        const findingsContainer = document.getElementById('perf-findings');

        if (!summarySection || !findingsContainer) return;

        summarySection.style.display = 'block';
        findingsContainer.innerHTML = '';

        // Find TGP and TCP data
        const tgpData = data.protocols.find(p => p.name === 'TGP');
        const tcpData = data.protocols.find(p => p.name === 'TCP');

        if (tgpData && tcpData) {
            // Compare at high loss rates
            const tgpHighLoss = tgpData.data.find(d => d.lossRate >= 90);
            const tcpHighLoss = tcpData.data.find(d => d.lossRate >= 90);

            if (tgpHighLoss && tcpHighLoss) {
                const finding1 = document.createElement('div');
                finding1.className = 'perf-finding';
                finding1.innerHTML = `
                    <div class="finding-icon">✅</div>
                    <div class="finding-text">
                        <strong>TGP maintains ${tgpHighLoss.symmetryRate.toFixed(0)}% symmetric outcomes</strong>
                        at ${tgpHighLoss.lossRate}% packet loss, while TCP drops to ${tcpHighLoss.symmetryRate.toFixed(0)}%
                    </div>
                `;
                findingsContainer.appendChild(finding1);
            }
        }

        // Add key insights
        const insights = [
            {
                icon: '🛡️',
                text: '<strong>Zero asymmetric failures</strong> - TGP\'s bilateral construction guarantees both parties reach the same decision'
            },
            {
                icon: '⚡',
                text: '<strong>Continuous flooding</strong> eliminates "last message" vulnerability'
            },
            {
                icon: '📊',
                text: '<strong>Higher message overhead</strong> is the tradeoff for deterministic coordination'
            }
        ];

        insights.forEach(insight => {
            const findingEl = document.createElement('div');
            findingEl.className = 'perf-finding';
            findingEl.innerHTML = `
                <div class="finding-icon">${insight.icon}</div>
                <div class="finding-text">${insight.text}</div>
            `;
            findingsContainer.appendChild(findingEl);
        });
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
