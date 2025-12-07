/**
 * Why It Works - Tab 1 Sections 5-8
 *
 * Interactive visualizations explaining WHY the TGP protocol guarantees
 * symmetric outcomes through:
 *
 * Section 5: Bilateral Construction Graph - shows proof dependencies
 * Section 6: No Last Message Comparison - contrasts TGP with ACK chains
 * Section 7: Knot Metaphor - visual metaphor for mutual constructibility
 * Section 8: Impact Visualization - real-world applications
 */

import * as d3 from 'd3';
import { createAnimationControls } from './components/animation-controls.js';

// =============================================================================
// Section 5: Bilateral Construction Graph
// =============================================================================

export class BilateralConstructionGraph {
    /**
     * Visualizes the bilateral construction property as a dependency graph.
     *
     * Key insight: Q_A exists → T_B exists → D_A received → Q_B constructible
     *
     * The graph shows how proof dependencies form a symmetric structure
     * where neither party can reach Q without the other being able to.
     */
    constructor(containerId) {
        this.container = document.getElementById(containerId);
        if (!this.container) return;

        this.width = 700;
        this.height = 500;
        this.animationStep = 0;
        this.isPlaying = false;

        // Animation speed control
        this.speed = 1.0;
        this.isPaused = false;
        this.controls = null;

        this.colors = {
            alice: '#58a6ff',
            bob: '#3fb950',
            dependency: '#a371f7',
            highlight: '#f0883e',
            muted: '#6e7681',
            text: '#f0f6fc',
            bg: '#161b22'
        };

        this.nodes = [
            // Alice's proofs (left side)
            { id: 'C_A', label: 'C_A', party: 'alice', level: 0, x: 150, y: 100 },
            { id: 'D_A', label: 'D_A', party: 'alice', level: 1, x: 150, y: 200 },
            { id: 'T_A', label: 'T_A', party: 'alice', level: 2, x: 150, y: 300 },
            { id: 'Q_A', label: 'Q_A', party: 'alice', level: 3, x: 150, y: 400 },
            // Bob's proofs (right side)
            { id: 'C_B', label: 'C_B', party: 'bob', level: 0, x: 550, y: 100 },
            { id: 'D_B', label: 'D_B', party: 'bob', level: 1, x: 550, y: 200 },
            { id: 'T_B', label: 'T_B', party: 'bob', level: 2, x: 550, y: 300 },
            { id: 'Q_B', label: 'Q_B', party: 'bob', level: 3, x: 550, y: 400 }
        ];

        // Dependencies showing what each proof requires
        this.links = [
            // D requires own C + other's C
            { source: 'C_A', target: 'D_A', type: 'embed' },
            { source: 'C_B', target: 'D_A', type: 'receive' },
            { source: 'C_B', target: 'D_B', type: 'embed' },
            { source: 'C_A', target: 'D_B', type: 'receive' },
            // T requires own D + other's D
            { source: 'D_A', target: 'T_A', type: 'embed' },
            { source: 'D_B', target: 'T_A', type: 'receive' },
            { source: 'D_B', target: 'T_B', type: 'embed' },
            { source: 'D_A', target: 'T_B', type: 'receive' },
            // Q requires own T + other's T
            { source: 'T_A', target: 'Q_A', type: 'embed' },
            { source: 'T_B', target: 'Q_A', type: 'receive' },
            { source: 'T_B', target: 'Q_B', type: 'embed' },
            { source: 'T_A', target: 'Q_B', type: 'receive' },
            // The bilateral implication (the key insight!)
            { source: 'Q_A', target: 'Q_B', type: 'implies', bidirectional: true }
        ];

        this.init();
    }

    init() {
        // Clear container
        this.container.innerHTML = '';

        // Create animation controls
        this.controls = createAnimationControls({
            container: this.container,
            defaultSpeed: 1.0,
            minSpeed: 0.25,
            maxSpeed: 2.0,
            step: 0.25,
            showStepControls: true,
            onSpeedChange: (speed) => {
                this.speed = speed;
            },
            onPlayPause: (isPlaying) => {
                this.isPlaying = isPlaying;
                this.isPaused = !isPlaying;
                if (isPlaying) {
                    this.animate();
                }
            },
            onReset: () => {
                this.reset();
            },
            onStep: (direction) => {
                if (direction > 0 && this.animationStep < this.getMaxSteps()) {
                    this.animationStep++;
                    this.updateVisualization();
                } else if (direction < 0 && this.animationStep > 0) {
                    this.animationStep--;
                    this.updateVisualization();
                }
            }
        });

        // Add main container
        const contentDiv = document.createElement('div');
        contentDiv.innerHTML = `
            <div class="bilateral-header">
                <h3>Bilateral Construction Property</h3>
                <p class="bilateral-subtitle">Why Q_A ↔ Q_B: mutual constructibility</p>
            </div>
            <svg id="bilateral-svg" viewBox="0 0 ${this.width} ${this.height}"></svg>
            <div class="bilateral-explanation" id="bilateral-explanation">
                <p>Use controls above to step through the proof dependencies.</p>
            </div>
        `;
        this.container.appendChild(contentDiv);

        this.svg = d3.select('#bilateral-svg');
        this.setupSVG();
        this.drawGraph();

        // Define animation steps
        this.steps = [
            {
                highlight: ['C_A', 'C_B'],
                links: [],
                text: '<strong>Step 1:</strong> Both parties generate commitments C_A and C_B independently.'
            },
            {
                highlight: ['D_A', 'D_B'],
                links: ['C_A→D_A', 'C_B→D_A', 'C_B→D_B', 'C_A→D_B'],
                text: '<strong>Step 2:</strong> Each constructs D by embedding their C with the received C.'
            },
            {
                highlight: ['T_A', 'T_B'],
                links: ['D_A→T_A', 'D_B→T_A', 'D_B→T_B', 'D_A→T_B'],
                text: '<strong>Step 3:</strong> Each constructs T by embedding their D with the received D.'
            },
            {
                highlight: ['Q_A', 'Q_B'],
                links: ['T_A→Q_A', 'T_B→Q_A', 'T_B→Q_B', 'T_A→Q_B'],
                text: '<strong>Step 4:</strong> Each constructs Q by embedding their T with the received T.'
            },
            {
                highlight: ['Q_A', 'Q_B'],
                links: ['Q_A↔Q_B'],
                text: '<strong>Key Insight:</strong> Q_A exists → contains T_B → Bob had D_A → Bob can construct Q_B!<br><em>Neither Q can exist without the other being constructible.</em>'
            }
        ];
    }

    setupSVG() {
        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', this.colors.bg)
            .attr('rx', 12);

        // Define arrow markers
        const defs = this.svg.append('defs');

        // Regular arrow
        defs.append('marker')
            .attr('id', 'arrow')
            .attr('viewBox', '0 -5 10 10')
            .attr('refX', 20)
            .attr('refY', 0)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M0,-5L10,0L0,5')
            .attr('fill', this.colors.muted);

        // Bidirectional arrow for implication
        defs.append('marker')
            .attr('id', 'arrow-implies')
            .attr('viewBox', '0 -5 10 10')
            .attr('refX', 20)
            .attr('refY', 0)
            .attr('markerWidth', 8)
            .attr('markerHeight', 8)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M0,-5L10,0L0,5')
            .attr('fill', this.colors.highlight);

        // Party labels
        this.svg.append('text')
            .attr('x', 150)
            .attr('y', 50)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.alice)
            .attr('font-size', '16px')
            .attr('font-weight', 'bold')
            .text('Alice');

        this.svg.append('text')
            .attr('x', 550)
            .attr('y', 50)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.bob)
            .attr('font-size', '16px')
            .attr('font-weight', 'bold')
            .text('Bob');

        // Level labels
        const levels = ['Commitment', 'Double Proof', 'Triple Proof', 'Quad Proof'];
        levels.forEach((label, i) => {
            this.svg.append('text')
                .attr('x', 350)
                .attr('y', 105 + i * 100)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.muted)
                .attr('font-size', '11px')
                .text(label);
        });

        // Groups for layers
        this.linkGroup = this.svg.append('g').attr('class', 'links');
        this.nodeGroup = this.svg.append('g').attr('class', 'nodes');
    }

    drawGraph() {
        const nodeMap = new Map(this.nodes.map(n => [n.id, n]));

        // Draw links
        this.linkGroup.selectAll('.link')
            .data(this.links)
            .enter()
            .append('line')
            .attr('class', d => `link link-${d.type}`)
            .attr('x1', d => nodeMap.get(d.source).x)
            .attr('y1', d => nodeMap.get(d.source).y)
            .attr('x2', d => nodeMap.get(d.target).x)
            .attr('y2', d => nodeMap.get(d.target).y)
            .attr('stroke', d => d.type === 'implies' ? this.colors.highlight : this.colors.muted)
            .attr('stroke-width', d => d.type === 'implies' ? 3 : 1.5)
            .attr('stroke-dasharray', d => d.type === 'receive' ? '4,4' : 'none')
            .attr('marker-end', d => d.type === 'implies' ? 'url(#arrow-implies)' : 'url(#arrow)')
            .attr('opacity', 0.3);

        // Draw nodes
        const nodeGroups = this.nodeGroup.selectAll('.node')
            .data(this.nodes)
            .enter()
            .append('g')
            .attr('class', 'node')
            .attr('transform', d => `translate(${d.x}, ${d.y})`);

        nodeGroups.append('circle')
            .attr('r', 25)
            .attr('fill', d => d.party === 'alice' ? this.colors.alice : this.colors.bob)
            .attr('fill-opacity', 0.2)
            .attr('stroke', d => d.party === 'alice' ? this.colors.alice : this.colors.bob)
            .attr('stroke-width', 2);

        nodeGroups.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', 5)
            .attr('fill', this.colors.text)
            .attr('font-family', "'JetBrains Mono', monospace")
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text(d => d.label);
    }

    getMaxSteps() {
        return this.steps.length;
    }

    updateVisualization() {
        if (this.animationStep >= 0 && this.animationStep < this.steps.length) {
            this.showStep(this.steps[this.animationStep]);
        }
    }

    animate() {
        if (this.isPlaying) return;
        this.isPlaying = true;
        this.animationStep = 0;

        const runStep = () => {
            if (!this.isPlaying || this.animationStep >= this.steps.length) {
                this.isPlaying = false;
                if (this.controls) {
                    this.controls.setPlaying(false);
                }
                return;
            }

            // Respect pause state
            if (this.isPaused) {
                setTimeout(runStep, 100);
                return;
            }

            this.showStep(this.steps[this.animationStep]);
            this.animationStep++;

            // Apply speed multiplier (inverse: higher speed = shorter interval)
            const adjustedInterval = 2500 / this.speed;
            setTimeout(runStep, adjustedInterval);
        };

        runStep();
    }

    showStep(step) {
        const explanation = document.getElementById('bilateral-explanation');
        if (explanation) {
            explanation.innerHTML = `<p>${step.text}</p>`;
        }

        // Highlight nodes
        this.nodeGroup.selectAll('.node circle')
            .transition()
            .duration(300)
            .attr('fill-opacity', d => step.highlight.includes(d.id) ? 0.8 : 0.2)
            .attr('stroke-width', d => step.highlight.includes(d.id) ? 3 : 2);

        // Highlight relevant links
        this.linkGroup.selectAll('.link')
            .transition()
            .duration(300)
            .attr('opacity', d => {
                const linkId = `${d.source}→${d.target}`;
                const biLinkId = `${d.source}↔${d.target}`;
                return step.links.includes(linkId) || step.links.includes(biLinkId) ? 1 : 0.1;
            })
            .attr('stroke-width', d => {
                const linkId = `${d.source}→${d.target}`;
                const biLinkId = `${d.source}↔${d.target}`;
                if (step.links.includes(linkId) || step.links.includes(biLinkId)) {
                    return d.type === 'implies' ? 4 : 2.5;
                }
                return d.type === 'implies' ? 3 : 1.5;
            });
    }

    reset() {
        this.isPlaying = false;
        this.animationStep = 0;
        this.isPaused = false;

        if (this.controls) {
            this.controls.setPlaying(false);
        }

        const explanation = document.getElementById('bilateral-explanation');
        if (explanation) {
            explanation.innerHTML = '<p>Use controls above to step through the proof dependencies.</p>';
        }

        this.nodeGroup.selectAll('.node circle')
            .transition()
            .duration(300)
            .attr('fill-opacity', 0.2)
            .attr('stroke-width', 2);

        this.linkGroup.selectAll('.link')
            .transition()
            .duration(300)
            .attr('opacity', 0.3)
            .attr('stroke-width', d => d.type === 'implies' ? 3 : 1.5);
    }
}


// =============================================================================
// Section 6: No Last Message Comparison
// =============================================================================

export class NoLastMessageComparison {
    /**
     * Side-by-side comparison of ACK chains (infinite regress) vs TGP flooding.
     *
     * Traditional: MSG → ACK → ACK-ACK → ACK-ACK-ACK → ... (never ends)
     * TGP: Continuous flooding means ANY instance suffices, no "last message"
     */
    constructor(containerId) {
        this.container = document.getElementById(containerId);
        if (!this.container) return;

        this.width = 800;
        this.height = 300;
        this.isPlaying = false;

        this.colors = {
            traditional: '#f85149',  // Red for problem
            tgp: '#3fb950',         // Green for solution
            message: '#58a6ff',
            lost: '#6e7681',
            text: '#f0f6fc',
            bg: '#161b22'
        };

        this.init();
    }

    init() {
        this.container.innerHTML = `
            <div class="no-last-message-container">
                <div class="comparison-header">
                    <h3>Why "No Last Message" Matters</h3>
                </div>
                <div class="comparison-panels">
                    <div class="comparison-panel traditional">
                        <h4>Traditional ACK Chain</h4>
                        <p class="problem-label">The Problem: Infinite Regress</p>
                        <svg id="ack-chain-svg" viewBox="0 0 350 250"></svg>
                        <div class="panel-note danger">
                            <span>Every message could be "the last one" that fails</span>
                        </div>
                    </div>
                    <div class="comparison-panel tgp">
                        <h4>TGP Continuous Flooding</h4>
                        <p class="solution-label">The Solution: No Special Message</p>
                        <svg id="flooding-svg" viewBox="0 0 350 250"></svg>
                        <div class="panel-note success">
                            <span>Any single delivery suffices - no message is "last"</span>
                        </div>
                    </div>
                </div>
                <div class="comparison-controls">
                    <button id="comparison-play" class="primary">Show Comparison</button>
                    <button id="comparison-reset">Reset</button>
                </div>
            </div>
        `;

        this.ackSvg = d3.select('#ack-chain-svg');
        this.floodSvg = d3.select('#flooding-svg');
        this.setupAckChain();
        this.setupFlooding();
        this.bindEvents();
    }

    setupAckChain() {
        // Background
        this.ackSvg.append('rect')
            .attr('width', 350)
            .attr('height', 250)
            .attr('fill', this.colors.bg)
            .attr('rx', 8);

        // Alice and Bob
        this.ackSvg.append('circle').attr('cx', 50).attr('cy', 125).attr('r', 20)
            .attr('fill', this.colors.message).attr('opacity', 0.3);
        this.ackSvg.append('text').attr('x', 50).attr('y', 130)
            .attr('text-anchor', 'middle').attr('fill', this.colors.text)
            .attr('font-size', '12px').text('A');

        this.ackSvg.append('circle').attr('cx', 300).attr('cy', 125).attr('r', 20)
            .attr('fill', this.colors.message).attr('opacity', 0.3);
        this.ackSvg.append('text').attr('x', 300).attr('y', 130)
            .attr('text-anchor', 'middle').attr('fill', this.colors.text)
            .attr('font-size', '12px').text('B');

        // Message group
        this.ackMessages = this.ackSvg.append('g').attr('class', 'ack-messages');
    }

    setupFlooding() {
        // Background
        this.floodSvg.append('rect')
            .attr('width', 350)
            .attr('height', 250)
            .attr('fill', this.colors.bg)
            .attr('rx', 8);

        // Alice and Bob
        this.floodSvg.append('circle').attr('cx', 50).attr('cy', 125).attr('r', 20)
            .attr('fill', this.colors.tgp).attr('opacity', 0.3);
        this.floodSvg.append('text').attr('x', 50).attr('y', 130)
            .attr('text-anchor', 'middle').attr('fill', this.colors.text)
            .attr('font-size', '12px').text('A');

        this.floodSvg.append('circle').attr('cx', 300).attr('cy', 125).attr('r', 20)
            .attr('fill', this.colors.tgp).attr('opacity', 0.3);
        this.floodSvg.append('text').attr('x', 300).attr('y', 130)
            .attr('text-anchor', 'middle').attr('fill', this.colors.text)
            .attr('font-size', '12px').text('B');

        // Flood group
        this.floodMessages = this.floodSvg.append('g').attr('class', 'flood-messages');
    }

    bindEvents() {
        const playBtn = document.getElementById('comparison-play');
        const resetBtn = document.getElementById('comparison-reset');

        if (playBtn) {
            playBtn.addEventListener('click', () => this.playComparison());
        }
        if (resetBtn) {
            resetBtn.addEventListener('click', () => this.reset());
        }
    }

    playComparison() {
        if (this.isPlaying) return;
        this.isPlaying = true;
        this.reset();

        // Animate ACK chain (showing the problem)
        this.animateAckChain();

        // Animate flooding (showing the solution)
        this.animateFlooding();
    }

    animateAckChain() {
        const messages = [
            { from: 50, to: 300, y: 60, label: 'MSG', lost: false },
            { from: 300, to: 50, y: 90, label: 'ACK', lost: false },
            { from: 50, to: 300, y: 120, label: 'ACK²', lost: false },
            { from: 300, to: 50, y: 150, label: 'ACK³', lost: true },  // This one fails!
            { from: 50, to: 300, y: 180, label: 'ACK⁴', lost: true, phantom: true },
            { from: 300, to: 50, y: 210, label: '...∞', lost: true, phantom: true }
        ];

        messages.forEach((msg, i) => {
            setTimeout(() => {
                if (msg.phantom) {
                    // Show as dotted/faded to indicate never sent
                    this.ackMessages.append('line')
                        .attr('x1', msg.from)
                        .attr('y1', msg.y)
                        .attr('x2', msg.from)
                        .attr('y2', msg.y)
                        .attr('stroke', this.colors.lost)
                        .attr('stroke-width', 2)
                        .attr('stroke-dasharray', '4,4')
                        .transition()
                        .duration(500)
                        .attr('x2', msg.to);

                    this.ackMessages.append('text')
                        .attr('x', (msg.from + msg.to) / 2)
                        .attr('y', msg.y - 5)
                        .attr('text-anchor', 'middle')
                        .attr('fill', this.colors.lost)
                        .attr('font-size', '10px')
                        .attr('opacity', 0)
                        .text(msg.label)
                        .transition()
                        .delay(300)
                        .attr('opacity', 0.5);
                } else {
                    const line = this.ackMessages.append('line')
                        .attr('x1', msg.from)
                        .attr('y1', msg.y)
                        .attr('x2', msg.from)
                        .attr('y2', msg.y)
                        .attr('stroke', msg.lost ? this.colors.traditional : this.colors.message)
                        .attr('stroke-width', 2)
                        .transition()
                        .duration(500)
                        .attr('x2', msg.lost ? (msg.from + msg.to) / 2 : msg.to);

                    // Label
                    this.ackMessages.append('text')
                        .attr('x', (msg.from + msg.to) / 2)
                        .attr('y', msg.y - 5)
                        .attr('text-anchor', 'middle')
                        .attr('fill', msg.lost ? this.colors.traditional : this.colors.text)
                        .attr('font-size', '10px')
                        .attr('opacity', 0)
                        .text(msg.label + (msg.lost ? ' ✗' : ''))
                        .transition()
                        .delay(300)
                        .attr('opacity', 1);

                    if (msg.lost) {
                        // Add X marker
                        setTimeout(() => {
                            this.ackMessages.append('text')
                                .attr('x', (msg.from + msg.to) / 2)
                                .attr('y', msg.y + 5)
                                .attr('text-anchor', 'middle')
                                .attr('fill', this.colors.traditional)
                                .attr('font-size', '20px')
                                .text('💥')
                                .attr('opacity', 0)
                                .transition()
                                .attr('opacity', 1);
                        }, 600);
                    }
                }
            }, i * 800);
        });
    }

    animateFlooding() {
        // Show many parallel messages, some lost but one gets through
        const floods = [];
        for (let i = 0; i < 8; i++) {
            floods.push({
                from: i % 2 === 0 ? 50 : 300,
                to: i % 2 === 0 ? 300 : 50,
                y: 50 + i * 25,
                lost: Math.random() < 0.6,  // 60% loss rate
                delay: i * 150
            });
        }

        // Ensure at least one gets through for each direction
        floods[2].lost = false;  // A→B success
        floods[5].lost = false;  // B→A success

        floods.forEach((flood, i) => {
            setTimeout(() => {
                const line = this.floodMessages.append('line')
                    .attr('x1', flood.from)
                    .attr('y1', flood.y)
                    .attr('x2', flood.from)
                    .attr('y2', flood.y)
                    .attr('stroke', flood.lost ? this.colors.lost : this.colors.tgp)
                    .attr('stroke-width', flood.lost ? 1 : 2)
                    .attr('opacity', flood.lost ? 0.3 : 1)
                    .transition()
                    .duration(400)
                    .attr('x2', flood.lost ? (flood.from + flood.to) / 2 : flood.to);

                if (!flood.lost) {
                    // Add success marker
                    setTimeout(() => {
                        this.floodMessages.append('text')
                            .attr('x', flood.to)
                            .attr('y', flood.y - 10)
                            .attr('text-anchor', 'middle')
                            .attr('fill', this.colors.tgp)
                            .attr('font-size', '16px')
                            .text('✓')
                            .attr('opacity', 0)
                            .transition()
                            .attr('opacity', 1);
                    }, 400);
                }
            }, flood.delay);
        });

        // Add summary text
        setTimeout(() => {
            this.floodMessages.append('text')
                .attr('x', 175)
                .attr('y', 240)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.tgp)
                .attr('font-size', '11px')
                .text('Any one success ✓ = Full coordination')
                .attr('opacity', 0)
                .transition()
                .duration(500)
                .attr('opacity', 1);
        }, 1500);
    }

    reset() {
        this.isPlaying = false;
        this.ackMessages.selectAll('*').remove();
        this.floodMessages.selectAll('*').remove();
    }
}


// =============================================================================
// Section 7: Knot Metaphor Visualization
// =============================================================================

export class KnotMetaphorVisualization {
    /**
     * Visual metaphor: ACK chains are a chain, TGP is a knot.
     *
     * Chain: Each link is a potential failure point
     * Knot: The structure IS the proof - you can't have half a knot
     */
    constructor(containerId) {
        this.container = document.getElementById(containerId);
        if (!this.container) return;

        this.width = 800;
        this.height = 400;
        this.animationPhase = 0;

        this.colors = {
            chain: '#f85149',
            knot: '#3fb950',
            knotCenter: '#a371f7',
            text: '#f0f6fc',
            muted: '#6e7681',
            bg: '#161b22'
        };

        this.init();
    }

    init() {
        this.container.innerHTML = `
            <div class="knot-metaphor-container">
                <div class="knot-header">
                    <h3>The Knot, Not The Chain</h3>
                    <p class="knot-subtitle">TGP creates entanglement, not sequential dependency</p>
                </div>
                <div class="knot-comparison">
                    <div class="chain-side">
                        <svg id="chain-metaphor-svg" viewBox="0 0 350 300"></svg>
                        <div class="metaphor-label chain-label">
                            <strong>ACK Chain</strong>
                            <p>Break any link → chain fails</p>
                        </div>
                    </div>
                    <div class="vs-divider">
                        <span>vs</span>
                    </div>
                    <div class="knot-side">
                        <svg id="knot-metaphor-svg" viewBox="0 0 350 300"></svg>
                        <div class="metaphor-label knot-label">
                            <strong>TGP Knot</strong>
                            <p>Can't untie half a knot</p>
                        </div>
                    </div>
                </div>
                <div class="knot-insight">
                    <p>
                        <strong>Gray's chain goes outward forever, never landing.</strong><br>
                        <strong>TGP's knot goes inward forever, always landed.</strong>
                    </p>
                </div>
                <div class="knot-controls">
                    <button id="knot-animate" class="primary">Animate</button>
                    <button id="knot-reset">Reset</button>
                </div>
            </div>
        `;

        this.chainSvg = d3.select('#chain-metaphor-svg');
        this.knotSvg = d3.select('#knot-metaphor-svg');
        this.drawChain();
        this.drawKnot();
        this.bindEvents();
    }

    drawChain() {
        // Background
        this.chainSvg.append('rect')
            .attr('width', 350)
            .attr('height', 300)
            .attr('fill', this.colors.bg)
            .attr('rx', 12);

        // Chain links
        this.chainGroup = this.chainSvg.append('g').attr('class', 'chain-group');

        const linkCount = 6;
        const linkWidth = 40;
        const linkHeight = 25;
        const startX = 50;
        const startY = 80;

        for (let i = 0; i < linkCount; i++) {
            const x = startX + i * 45;
            const y = startY + (i % 2) * 20;

            this.chainGroup.append('ellipse')
                .attr('cx', x + linkWidth / 2)
                .attr('cy', y + linkHeight / 2)
                .attr('rx', linkWidth / 2)
                .attr('ry', linkHeight / 2)
                .attr('fill', 'none')
                .attr('stroke', this.colors.chain)
                .attr('stroke-width', 4)
                .attr('class', `chain-link-${i}`);

            // Label
            this.chainGroup.append('text')
                .attr('x', x + linkWidth / 2)
                .attr('y', y + linkHeight / 2 + 4)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.text)
                .attr('font-size', '10px')
                .text(i === 0 ? 'MSG' : `ACK${i}`);
        }

        // "Break point" marker
        this.chainGroup.append('text')
            .attr('x', 175)
            .attr('y', 180)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.chain)
            .attr('font-size', '12px')
            .text('↑ Potential break point');

        // Infinity arrow
        this.chainGroup.append('text')
            .attr('x', 320)
            .attr('y', 100)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '24px')
            .text('→∞');

        // Problem annotation
        this.chainSvg.append('text')
            .attr('x', 175)
            .attr('y', 250)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.chain)
            .attr('font-size', '11px')
            .attr('font-style', 'italic')
            .text('Always another link needed...');
    }

    drawKnot() {
        // Background
        this.knotSvg.append('rect')
            .attr('width', 350)
            .attr('height', 300)
            .attr('fill', this.colors.bg)
            .attr('rx', 12);

        this.knotGroup = this.knotSvg.append('g')
            .attr('class', 'knot-group')
            .attr('transform', 'translate(175, 140)');

        // Draw the "bilateral knot" - two interlocking loops
        const knotPath = this.knotGroup.append('g').attr('class', 'knot-loops');

        // Alice's loop (left, blue)
        knotPath.append('path')
            .attr('d', 'M-80,0 C-80,-60 -20,-60 0,-30 C20,0 20,60 -20,60 C-60,60 -80,30 -80,0')
            .attr('fill', 'none')
            .attr('stroke', '#58a6ff')
            .attr('stroke-width', 6)
            .attr('class', 'alice-loop');

        // Bob's loop (right, green)
        knotPath.append('path')
            .attr('d', 'M80,0 C80,-60 20,-60 0,-30 C-20,0 -20,60 20,60 C60,60 80,30 80,0')
            .attr('fill', 'none')
            .attr('stroke', this.colors.knot)
            .attr('stroke-width', 6)
            .attr('class', 'bob-loop');

        // Center crossing point (the "knot")
        knotPath.append('circle')
            .attr('cx', 0)
            .attr('cy', -30)
            .attr('r', 15)
            .attr('fill', this.colors.knotCenter)
            .attr('opacity', 0.8)
            .attr('class', 'knot-center');

        // Q labels
        knotPath.append('text')
            .attr('x', -60)
            .attr('y', 5)
            .attr('fill', '#58a6ff')
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('Q_A');

        knotPath.append('text')
            .attr('x', 45)
            .attr('y', 5)
            .attr('fill', this.colors.knot)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('Q_B');

        // Center label
        knotPath.append('text')
            .attr('x', 0)
            .attr('y', -25)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '10px')
            .attr('font-weight', 'bold')
            .text('↔');

        // Knot annotation
        this.knotSvg.append('text')
            .attr('x', 175)
            .attr('y', 250)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.knot)
            .attr('font-size', '11px')
            .attr('font-style', 'italic')
            .text('Neither loop exists without the other');
    }

    bindEvents() {
        const animateBtn = document.getElementById('knot-animate');
        const resetBtn = document.getElementById('knot-reset');

        if (animateBtn) {
            animateBtn.addEventListener('click', () => this.animate());
        }
        if (resetBtn) {
            resetBtn.addEventListener('click', () => this.reset());
        }
    }

    animate() {
        // Animate chain breaking
        this.chainSvg.select('.chain-link-3')
            .transition()
            .duration(500)
            .attr('stroke', '#ff0000')
            .attr('stroke-dasharray', '5,5')
            .transition()
            .duration(300)
            .attr('opacity', 0.3);

        // Add break indicator
        this.chainGroup.append('text')
            .attr('x', 185)
            .attr('y', 100)
            .attr('fill', '#ff0000')
            .attr('font-size', '24px')
            .text('💥')
            .attr('opacity', 0)
            .transition()
            .delay(300)
            .attr('opacity', 1);

        // Animate knot pulsing (showing strength)
        this.knotGroup.select('.knot-center')
            .transition()
            .duration(500)
            .attr('r', 20)
            .attr('opacity', 1)
            .transition()
            .duration(500)
            .attr('r', 15)
            .attr('opacity', 0.8)
            .transition()
            .duration(500)
            .attr('r', 20)
            .attr('opacity', 1)
            .transition()
            .duration(500)
            .attr('r', 15);

        // Pulse the loops
        this.knotGroup.selectAll('.alice-loop, .bob-loop')
            .transition()
            .duration(500)
            .attr('stroke-width', 8)
            .transition()
            .duration(500)
            .attr('stroke-width', 6);
    }

    reset() {
        // Reset chain
        this.chainSvg.select('.chain-link-3')
            .transition()
            .duration(300)
            .attr('stroke', this.colors.chain)
            .attr('stroke-dasharray', 'none')
            .attr('opacity', 1);

        this.chainGroup.selectAll('text').filter(function() {
            return d3.select(this).text() === '💥';
        }).remove();

        // Reset knot
        this.knotGroup.select('.knot-center')
            .transition()
            .duration(300)
            .attr('r', 15)
            .attr('opacity', 0.8);

        this.knotGroup.selectAll('.alice-loop, .bob-loop')
            .transition()
            .duration(300)
            .attr('stroke-width', 6);
    }
}


// =============================================================================
// Section 8: Impact Visualization
// =============================================================================

export class ImpactVisualization {
    /**
     * Shows real-world applications and impact of TGP.
     *
     * Categories:
     * - ToTG: TCP over TGP for satellite/mobile
     * - BFT: Byzantine consensus in 2 floods
     * - IoT: Mesh network coordination
     * - Finance: Payment channel finality
     */
    constructor(containerId) {
        this.container = document.getElementById(containerId);
        if (!this.container) return;

        this.applications = [
            {
                id: 'totg',
                title: 'TCP over TGP (ToTG)',
                icon: '🛰️',
                metric: '500x',
                metricLabel: 'throughput at 90% loss',
                description: 'Reliable transport for satellite, mobile, and high-loss networks',
                color: '#58a6ff'
            },
            {
                id: 'bft',
                title: 'BFT in 2 Floods',
                icon: '🔐',
                metric: '2',
                metricLabel: 'rounds to consensus',
                description: 'Byzantine fault tolerance without view-change or leader rotation',
                color: '#a371f7'
            },
            {
                id: 'iot',
                title: 'IoT Mesh Networks',
                icon: '📡',
                metric: '0',
                metricLabel: 'coordinator required',
                description: 'Decentralized coordination for sensor networks and smart devices',
                color: '#3fb950'
            },
            {
                id: 'finance',
                title: 'Payment Finality',
                icon: '💰',
                metric: '∞',
                metricLabel: 'cryptographic certainty',
                description: 'Atomic cross-chain swaps with provable coordination',
                color: '#d29922'
            }
        ];

        this.init();
    }

    init() {
        this.container.innerHTML = `
            <div class="impact-visualization-container">
                <div class="impact-header">
                    <h3>Real-World Impact</h3>
                    <p class="impact-subtitle">Applications enabled by deterministic coordination</p>
                </div>
                <div class="impact-grid">
                    ${this.applications.map(app => this.renderApplicationCard(app)).join('')}
                </div>
                <div class="impact-comparison">
                    <h4>Performance vs TCP (at 90%+ packet loss)</h4>
                    <div class="performance-bars">
                        <div class="perf-bar-group">
                            <span class="perf-label">TCP Throughput</span>
                            <div class="perf-bar tcp-bar">
                                <div class="perf-fill" style="width: 5%"></div>
                            </div>
                            <span class="perf-value">~5%</span>
                        </div>
                        <div class="perf-bar-group">
                            <span class="perf-label">TGP Throughput</span>
                            <div class="perf-bar tgp-bar">
                                <div class="perf-fill" style="width: 90%"></div>
                            </div>
                            <span class="perf-value">~90%</span>
                        </div>
                    </div>
                </div>
                <div class="impact-philosophy">
                    <blockquote>
                        <p>"The protocol doesn't <em>solve</em> the Two Generals Problem.<br>
                        The protocol <em>is</em> a structure where the problem has already solved itself."</p>
                        <footer>— 完成された使命 (Kansei sareta shimei)</footer>
                    </blockquote>
                </div>
            </div>
        `;

        this.animateCards();
    }

    renderApplicationCard(app) {
        return `
            <div class="impact-card" data-app="${app.id}" style="--accent-color: ${app.color}">
                <div class="card-icon">${app.icon}</div>
                <h4 class="card-title">${app.title}</h4>
                <div class="card-metric">
                    <span class="metric-value">${app.metric}</span>
                    <span class="metric-label">${app.metricLabel}</span>
                </div>
                <p class="card-description">${app.description}</p>
            </div>
        `;
    }

    animateCards() {
        // Stagger card entrance
        const cards = this.container.querySelectorAll('.impact-card');
        cards.forEach((card, i) => {
            card.style.opacity = '0';
            card.style.transform = 'translateY(20px)';

            setTimeout(() => {
                card.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
                card.style.opacity = '1';
                card.style.transform = 'translateY(0)';
            }, i * 150);
        });

        // Animate performance bars
        setTimeout(() => {
            const bars = this.container.querySelectorAll('.perf-fill');
            bars.forEach(bar => {
                const width = bar.style.width;
                bar.style.width = '0';
                bar.style.transition = 'width 1s ease-out';
                setTimeout(() => {
                    bar.style.width = width;
                }, 100);
            });
        }, 600);
    }
}


// =============================================================================
// Initialize All Sections
// =============================================================================

export function initWhyItWorks() {
    // Initialize each section when its container exists
    const bilateralContainer = document.getElementById('bilateral-construction-graph');
    const noLastMessageContainer = document.getElementById('no-last-message');
    const knotContainer = document.getElementById('knot-metaphor');
    const impactContainer = document.getElementById('impact-visualization');

    const visualizations = {};

    if (bilateralContainer) {
        visualizations.bilateral = new BilateralConstructionGraph('bilateral-construction-graph');
    }

    if (noLastMessageContainer) {
        visualizations.noLastMessage = new NoLastMessageComparison('no-last-message');
    }

    if (knotContainer) {
        visualizations.knot = new KnotMetaphorVisualization('knot-metaphor');
    }

    if (impactContainer) {
        visualizations.impact = new ImpactVisualization('impact-visualization');
    }

    return visualizations;
}
