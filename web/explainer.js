/**
 * Two Generals Protocol - Interactive Explainer
 *
 * Tab 1: The Problem (Sections 1-2)
 * - Section 1: Battlefield scene animation showing the military coordination problem
 * - Section 2: Infinite regress visualization showing why traditional ACKs fail
 *
 * These are the "hook" animations that explain why the problem matters.
 */

import * as d3 from 'd3';
import { Battlefield3D } from './components/battlefield-3d.js';

// =============================================================================
// Section 1: Battlefield Scene Animation (3D)
// Now using Three.js with homing pigeons
// =============================================================================

// =============================================================================
// Section 2: Infinite Regress Visualization
// =============================================================================

export class InfiniteRegressViz {
    /**
     * Shows why traditional ACK-based protocols fail:
     *
     * MSG → ACK → ACK-of-ACK → ACK-of-ACK-of-ACK → ...
     *
     * Every message could be "the last message" that gets lost,
     * leaving one party uncertain while the other acts.
     */
    constructor(container) {
        this.container = d3.select(container);
        this.width = 800;
        this.height = 500;
        this.svg = null;
        this.currentLevel = 0;
        this.maxLevels = 8;
        this.isAnimating = false;

        this.colors = {
            alice: '#58a6ff',
            bob: '#3fb950',
            message: '#d29922',
            ack: '#a371f7',
            lost: '#f85149',
            uncertainty: '#f85149',
            text: '#f0f6fc',
            muted: '#8b949e',
            bg: '#161b22'
        };
    }

    init() {
        this.container.html('');

        this.svg = this.container.append('svg')
            .attr('viewBox', `0 0 ${this.width} ${this.height}`)
            .attr('preserveAspectRatio', 'xMidYMid meet')
            .style('width', '100%')
            .style('max-width', '800px')
            .style('height', 'auto');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', '#0d1117')
            .attr('rx', 12);

        this.drawPartyLabels();
        this.drawTimeAxis();
        this.drawExplanation();
        this.currentLevel = 0;
    }

    drawPartyLabels() {
        // Alice column
        this.svg.append('rect')
            .attr('x', 50)
            .attr('y', 60)
            .attr('width', 100)
            .attr('height', 40)
            .attr('fill', this.colors.alice)
            .attr('fill-opacity', 0.2)
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 2)
            .attr('rx', 8);

        this.svg.append('text')
            .attr('x', 100)
            .attr('y', 85)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.alice)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('Alice');

        // Bob column
        this.svg.append('rect')
            .attr('x', this.width - 150)
            .attr('y', 60)
            .attr('width', 100)
            .attr('height', 40)
            .attr('fill', this.colors.bob)
            .attr('fill-opacity', 0.2)
            .attr('stroke', this.colors.bob)
            .attr('stroke-width', 2)
            .attr('rx', 8);

        this.svg.append('text')
            .attr('x', this.width - 100)
            .attr('y', 85)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.bob)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('Bob');

        // Vertical timeline lines
        this.svg.append('line')
            .attr('x1', 100)
            .attr('y1', 110)
            .attr('x2', 100)
            .attr('y2', this.height - 80)
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '4,4')
            .attr('opacity', 0.5);

        this.svg.append('line')
            .attr('x1', this.width - 100)
            .attr('y1', 110)
            .attr('x2', this.width - 100)
            .attr('y2', this.height - 80)
            .attr('stroke', this.colors.bob)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '4,4')
            .attr('opacity', 0.5);

        // Message container
        this.messageLayer = this.svg.append('g')
            .attr('class', 'messages');
    }

    drawTimeAxis() {
        // Time arrow on left
        this.svg.append('line')
            .attr('x1', 25)
            .attr('y1', 110)
            .attr('x2', 25)
            .attr('y2', this.height - 80)
            .attr('stroke', this.colors.muted)
            .attr('stroke-width', 1);

        this.svg.append('polygon')
            .attr('points', `25,${this.height - 80} 20,${this.height - 90} 30,${this.height - 90}`)
            .attr('fill', this.colors.muted);

        this.svg.append('text')
            .attr('x', 25)
            .attr('y', this.height - 65)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '10px')
            .text('time');
    }

    drawExplanation() {
        this.explanationGroup = this.svg.append('g')
            .attr('class', 'explanation')
            .attr('transform', `translate(${this.width / 2}, 30)`);

        this.explanationGroup.append('text')
            .attr('class', 'title')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '16px')
            .attr('font-weight', 'bold')
            .text('The Infinite Regress Problem');

        // Bottom explanation
        this.bottomExplanation = this.svg.append('g')
            .attr('class', 'bottom-explanation')
            .attr('transform', `translate(${this.width / 2}, ${this.height - 30})`);

        this.bottomExplanation.append('text')
            .attr('class', 'insight')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.uncertainty)
            .attr('font-size', '12px')
            .text('Every message could be "the last" - leaving one party uncertain forever.');
    }

    addMessage(level) {
        if (level > this.maxLevels) return;

        const isFromAlice = level % 2 === 0;
        const y = 130 + level * 40;
        const startX = isFromAlice ? 100 : this.width - 100;
        const endX = isFromAlice ? this.width - 100 : 100;
        const color = level === 0 ? this.colors.message : this.colors.ack;

        const messageGroup = this.messageLayer.append('g')
            .attr('class', `message level-${level}`)
            .attr('opacity', 0);

        // Message arrow
        const arrowLine = messageGroup.append('line')
            .attr('x1', startX)
            .attr('y1', y)
            .attr('x2', startX)
            .attr('y2', y)
            .attr('stroke', color)
            .attr('stroke-width', 2)
            .attr('marker-end', 'url(#arrow)');

        // Arrow marker
        const defs = this.svg.select('defs').empty() ? this.svg.append('defs') : this.svg.select('defs');
        if (defs.select('#arrow').empty()) {
            defs.append('marker')
                .attr('id', 'arrow')
                .attr('viewBox', '0 0 10 10')
                .attr('refX', 8)
                .attr('refY', 5)
                .attr('markerWidth', 6)
                .attr('markerHeight', 6)
                .attr('orient', 'auto-start-reverse')
                .append('path')
                .attr('d', 'M 0 0 L 10 5 L 0 10 z')
                .attr('fill', color);
        }

        // Message label
        const labelText = level === 0 ? 'MSG: "Attack at dawn?"' :
                         level === 1 ? 'ACK: "Got your message"' :
                         level === 2 ? 'ACK-ACK: "I know you got it"' :
                         level === 3 ? 'ACK\xB3: "I know you know..."' :
                         `ACK${this.superscript(level)}: "I know that you know..."`;

        const labelX = (startX + endX) / 2;
        messageGroup.append('text')
            .attr('x', labelX)
            .attr('y', y - 8)
            .attr('text-anchor', 'middle')
            .attr('fill', color)
            .attr('font-size', '10px')
            .text(labelText);

        // Thought bubble showing uncertainty
        if (level > 0) {
            const uncertainParty = isFromAlice ? this.width - 100 : 100;
            const thoughtX = isFromAlice ? this.width - 60 : 140;

            messageGroup.append('ellipse')
                .attr('cx', thoughtX)
                .attr('cy', y - 25)
                .attr('rx', 50)
                .attr('ry', 18)
                .attr('fill', this.colors.bg)
                .attr('stroke', this.colors.uncertainty)
                .attr('stroke-width', 1)
                .attr('stroke-dasharray', '2,2');

            messageGroup.append('text')
                .attr('x', thoughtX)
                .attr('y', y - 22)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.uncertainty)
                .attr('font-size', '8px')
                .text(isFromAlice ? 'Did they get it?' : 'Did they get it?');
        }

        // Animate in
        messageGroup.transition()
            .duration(300)
            .attr('opacity', 1);

        arrowLine.transition()
            .duration(800)
            .attr('x2', endX);

        this.currentLevel = level;
    }

    superscript(n) {
        const sups = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
        return String(n).split('').map(d => sups[parseInt(d)]).join('');
    }

    showLostMessage(level) {
        const isFromAlice = level % 2 === 0;
        const y = 130 + level * 40;
        const startX = isFromAlice ? 100 : this.width - 100;
        const lossX = (100 + this.width - 100) / 2;
        const color = this.colors.lost;

        const lostGroup = this.messageLayer.append('g')
            .attr('class', `lost-message level-${level}`);

        // Broken arrow
        lostGroup.append('line')
            .attr('x1', startX)
            .attr('y1', y)
            .attr('x2', lossX)
            .attr('y2', y)
            .attr('stroke', color)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '4,4');

        // X mark
        lostGroup.append('text')
            .attr('x', lossX)
            .attr('y', y + 5)
            .attr('text-anchor', 'middle')
            .attr('fill', color)
            .attr('font-size', '20px')
            .attr('font-weight', 'bold')
            .text('X');

        // "LOST!" label
        lostGroup.append('text')
            .attr('x', lossX)
            .attr('y', y - 15)
            .attr('text-anchor', 'middle')
            .attr('fill', color)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('LOST!');

        // Update bottom text
        this.bottomExplanation.select('.insight')
            .text(isFromAlice ?
                'Alice doesn\'t know if Bob got her last message. Bob waits. Nobody attacks.' :
                'Bob doesn\'t know if Alice got his ACK. He\'s uncertain. Coordination fails.');
    }

    runDemo() {
        this.reset();
        this.isAnimating = true;

        let level = 0;
        const addNext = () => {
            if (!this.isAnimating || level > 5) return;

            this.addMessage(level);
            level++;

            if (level <= 5) {
                setTimeout(addNext, 1200);
            } else {
                // Show the "last message" getting lost
                setTimeout(() => {
                    this.showLostMessage(level);
                }, 1500);
            }
        };

        setTimeout(addNext, 500);
    }

    stepForward() {
        if (this.currentLevel < this.maxLevels) {
            this.addMessage(this.currentLevel + 1);
        }
    }

    stop() {
        this.isAnimating = false;
    }

    reset() {
        this.stop();
        this.currentLevel = 0;
        this.messageLayer.selectAll('*').remove();
        this.bottomExplanation.select('.insight')
            .text('Every message could be "the last" - leaving one party uncertain forever.');
    }
}

// =============================================================================
// Explainer Controller
// =============================================================================

export class ExplainerController {
    /**
     * Orchestrates the explainer sections and handles navigation.
     */
    constructor() {
        this.currentSection = 0;
        this.sections = [];
        this.battlefield = null;
        this.infiniteRegress = null;
        this.proofMerging = null;
        this.phaseWalkthrough = null;
    }

    init() {
        // Initialize section visualizations
        const battlefieldContainer = document.getElementById('battlefield-scene');
        const regressContainer = document.getElementById('infinite-regress');

        if (battlefieldContainer) {
            this.battlefield = new Battlefield3D(battlefieldContainer);
            // Battlefield3D calls init() in constructor
            this.sections.push(this.battlefield);
        }

        if (regressContainer) {
            this.infiniteRegress = new InfiniteRegressViz(regressContainer);
            this.infiniteRegress.init();
            this.sections.push(this.infiniteRegress);
        }

        // Initialize Sections 3-4: The Solution
        this.initSolutionSections();

        this.bindEvents();
    }

    bindEvents() {
        // Navigation buttons
        document.querySelectorAll('[data-section-action]').forEach(btn => {
            btn.addEventListener('click', (e) => {
                const action = e.target.dataset.sectionAction;
                this.handleAction(action);
            });
        });

        // Auto-play toggles
        document.querySelectorAll('[data-autoplay]').forEach(btn => {
            btn.addEventListener('click', (e) => {
                const target = e.target.dataset.autoplay;
                this.toggleAutoplay(target);
            });
        });
    }

    handleAction(action) {
        switch (action) {
            case 'start-battlefield':
                this.battlefield?.startScenario('dilemma');
                break;
            case 'stop-battlefield':
                this.battlefield?.stop();
                break;
            case 'reset-battlefield':
                this.battlefield?.reset();
                break;
            case 'run-regress':
                this.infiniteRegress?.runDemo();
                break;
            case 'step-regress':
                this.infiniteRegress?.stepForward();
                break;
            case 'reset-regress':
                this.infiniteRegress?.reset();
                break;
        }
    }

    toggleAutoplay(target) {
        if (target === 'battlefield') {
            if (this.battlefield?.isAnimating) {
                this.battlefield.stop();
            } else {
                this.battlefield?.startScenario('dilemma');
            }
        } else if (target === 'regress') {
            if (this.infiniteRegress?.isAnimating) {
                this.infiniteRegress.stop();
            } else {
                this.infiniteRegress?.runDemo();
            }
        }
    }

    goToSection(index) {
        this.currentSection = index;
        // Update UI to show current section
        document.querySelectorAll('.explainer-section').forEach((el, i) => {
            el.classList.toggle('active', i === index);
        });
    }

    next() {
        if (this.currentSection < this.sections.length - 1) {
            this.goToSection(this.currentSection + 1);
        }
    }

    prev() {
        if (this.currentSection > 0) {
            this.goToSection(this.currentSection - 1);
        }
    }
}

// =============================================================================
// Section 3: Proof Merging Animation
// =============================================================================

export class ProofMergingAnimation {
    /**
     * Animated visualization showing how proofs embed at each level:
     *
     * C_A and C_B are standalone commitments
     * D_A embeds (C_A + C_B) signed by Alice
     * T_A embeds (D_A + D_B) signed by Alice
     * Q_A embeds (T_A + T_B) signed by Alice
     *
     * The key insight: receiving T_B gives you D_A and D_B for free (nested inside)
     */
    constructor(container) {
        this.container = d3.select(container);
        this.width = 800;
        this.height = 500;
        this.svg = null;
        this.currentStep = 0;
        this.isAnimating = false;
        this.animationTimer = null;

        this.colors = {
            alice: '#58a6ff',
            bob: '#3fb950',
            embedding: '#a371f7',
            fixpoint: '#f0883e',
            text: '#f0f6fc',
            muted: '#8b949e',
            bg: '#0d1117'
        };

        // Animation steps showing proof evolution
        this.steps = [
            {
                title: 'Initial State',
                description: 'Alice and Bob each generate their commitment.',
                proofs: [
                    { id: 'C_A', party: 'alice', level: 0, contains: [] },
                    { id: 'C_B', party: 'bob', level: 0, contains: [] }
                ]
            },
            {
                title: 'Commitments Exchanged',
                description: 'Each party receives the other\'s commitment through flooding.',
                proofs: [
                    { id: 'C_A', party: 'alice', level: 0, contains: [], sentTo: 'bob' },
                    { id: 'C_B', party: 'bob', level: 0, contains: [], sentTo: 'alice' }
                ]
            },
            {
                title: 'Double Proofs Created',
                description: 'Each party creates D by signing both commitments together.',
                proofs: [
                    { id: 'D_A', party: 'alice', level: 1, contains: ['C_A', 'C_B'] },
                    { id: 'D_B', party: 'bob', level: 1, contains: ['C_A', 'C_B'] }
                ]
            },
            {
                title: 'Double Proofs Exchanged',
                description: 'Each party receives the other\'s double proof.',
                proofs: [
                    { id: 'D_A', party: 'alice', level: 1, contains: ['C_A', 'C_B'], sentTo: 'bob' },
                    { id: 'D_B', party: 'bob', level: 1, contains: ['C_A', 'C_B'], sentTo: 'alice' }
                ]
            },
            {
                title: 'Triple Proofs Created',
                description: 'Each party creates T by signing both double proofs together.',
                proofs: [
                    { id: 'T_A', party: 'alice', level: 2, contains: ['D_A', 'D_B'] },
                    { id: 'T_B', party: 'bob', level: 2, contains: ['D_A', 'D_B'] }
                ]
            },
            {
                title: 'Triple Proofs Exchanged',
                description: 'Each party receives the other\'s triple proof.',
                proofs: [
                    { id: 'T_A', party: 'alice', level: 2, contains: ['D_A', 'D_B'], sentTo: 'bob' },
                    { id: 'T_B', party: 'bob', level: 2, contains: ['D_A', 'D_B'], sentTo: 'alice' }
                ]
            },
            {
                title: 'Quaternary Proofs - FIXPOINT!',
                description: 'Both parties can now construct Q. The bilateral construction property ensures symmetric completion.',
                proofs: [
                    { id: 'Q_A', party: 'alice', level: 3, contains: ['T_A', 'T_B'], isFixpoint: true },
                    { id: 'Q_B', party: 'bob', level: 3, contains: ['T_A', 'T_B'], isFixpoint: true }
                ]
            },
            {
                title: 'The Self-Certifying Property',
                description: 'Q contains all previous proofs embedded within it. Having Q proves common knowledge.',
                proofs: [
                    { id: 'Q_A', party: 'alice', level: 3, contains: ['T_A', 'T_B', 'D_A', 'D_B', 'C_A', 'C_B'], isFixpoint: true, expanded: true },
                    { id: 'Q_B', party: 'bob', level: 3, contains: ['T_A', 'T_B', 'D_A', 'D_B', 'C_A', 'C_B'], isFixpoint: true, expanded: true }
                ]
            }
        ];
    }

    init() {
        this.container.html('');

        this.svg = this.container.append('svg')
            .attr('viewBox', `0 0 ${this.width} ${this.height}`)
            .attr('preserveAspectRatio', 'xMidYMid meet')
            .style('width', '100%')
            .style('max-width', '800px')
            .style('height', 'auto');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', this.colors.bg)
            .attr('rx', 12);

        this.drawHeader();
        this.drawPartyZones();
        this.proofLayer = this.svg.append('g').attr('class', 'proofs');
        this.drawControls();

        this.showStep(0);
    }

    drawHeader() {
        this.headerGroup = this.svg.append('g')
            .attr('class', 'header')
            .attr('transform', 'translate(400, 30)');

        this.headerGroup.append('text')
            .attr('class', 'step-title')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '18px')
            .attr('font-weight', 'bold')
            .text('Proof Merging Animation');

        this.headerGroup.append('text')
            .attr('class', 'step-description')
            .attr('y', 25)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '13px')
            .text('Watch how proofs embed into each other');

        // Step counter
        this.headerGroup.append('text')
            .attr('class', 'step-counter')
            .attr('y', 50)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '11px')
            .text(`Step 1 of ${this.steps.length}`);
    }

    drawPartyZones() {
        // Alice zone (left)
        this.svg.append('rect')
            .attr('x', 20)
            .attr('y', 80)
            .attr('width', 360)
            .attr('height', 320)
            .attr('fill', this.colors.alice)
            .attr('fill-opacity', 0.05)
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 1)
            .attr('stroke-opacity', 0.3)
            .attr('rx', 8);

        this.svg.append('text')
            .attr('x', 200)
            .attr('y', 100)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.alice)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('ALICE');

        // Bob zone (right)
        this.svg.append('rect')
            .attr('x', 420)
            .attr('y', 80)
            .attr('width', 360)
            .attr('height', 320)
            .attr('fill', this.colors.bob)
            .attr('fill-opacity', 0.05)
            .attr('stroke', this.colors.bob)
            .attr('stroke-width', 1)
            .attr('stroke-opacity', 0.3)
            .attr('rx', 8);

        this.svg.append('text')
            .attr('x', 600)
            .attr('y', 100)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.bob)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('BOB');

        // Channel indicator
        this.svg.append('text')
            .attr('x', 400)
            .attr('y', 240)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '11px')
            .text('Lossy Channel');

        this.svg.append('line')
            .attr('x1', 385)
            .attr('y1', 250)
            .attr('x2', 385)
            .attr('y2', 350)
            .attr('stroke', this.colors.muted)
            .attr('stroke-width', 1)
            .attr('stroke-dasharray', '4,4');

        this.svg.append('line')
            .attr('x1', 415)
            .attr('y1', 250)
            .attr('x2', 415)
            .attr('y2', 350)
            .attr('stroke', this.colors.muted)
            .attr('stroke-width', 1)
            .attr('stroke-dasharray', '4,4');
    }

    drawControls() {
        // Control panel at bottom
        const controlY = this.height - 50;

        // Previous button
        this.svg.append('rect')
            .attr('class', 'control-btn prev-btn')
            .attr('x', 250)
            .attr('y', controlY)
            .attr('width', 80)
            .attr('height', 35)
            .attr('fill', '#21262d')
            .attr('stroke', '#30363d')
            .attr('stroke-width', 1)
            .attr('rx', 6)
            .style('cursor', 'pointer')
            .on('click', () => this.prevStep());

        this.svg.append('text')
            .attr('class', 'control-text')
            .attr('x', 290)
            .attr('y', controlY + 22)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .text('← Prev')
            .style('pointer-events', 'none');

        // Play/Pause button
        this.playBtn = this.svg.append('rect')
            .attr('class', 'control-btn play-btn')
            .attr('x', 350)
            .attr('y', controlY)
            .attr('width', 100)
            .attr('height', 35)
            .attr('fill', this.colors.alice)
            .attr('fill-opacity', 0.2)
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 1)
            .attr('rx', 6)
            .style('cursor', 'pointer')
            .on('click', () => this.toggleAutoPlay());

        this.playText = this.svg.append('text')
            .attr('class', 'control-text play-text')
            .attr('x', 400)
            .attr('y', controlY + 22)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.alice)
            .attr('font-size', '12px')
            .text('▶ Auto-play')
            .style('pointer-events', 'none');

        // Next button
        this.svg.append('rect')
            .attr('class', 'control-btn next-btn')
            .attr('x', 470)
            .attr('y', controlY)
            .attr('width', 80)
            .attr('height', 35)
            .attr('fill', '#21262d')
            .attr('stroke', '#30363d')
            .attr('stroke-width', 1)
            .attr('rx', 6)
            .style('cursor', 'pointer')
            .on('click', () => this.nextStep());

        this.svg.append('text')
            .attr('class', 'control-text')
            .attr('x', 510)
            .attr('y', controlY + 22)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .text('Next →')
            .style('pointer-events', 'none');
    }

    showStep(stepIndex) {
        this.currentStep = Math.max(0, Math.min(stepIndex, this.steps.length - 1));
        const step = this.steps[this.currentStep];

        // Update header
        this.headerGroup.select('.step-title')
            .transition()
            .duration(300)
            .attr('opacity', 0)
            .transition()
            .duration(300)
            .text(step.title)
            .attr('opacity', 1);

        this.headerGroup.select('.step-description')
            .transition()
            .duration(300)
            .text(step.description);

        this.headerGroup.select('.step-counter')
            .text(`Step ${this.currentStep + 1} of ${this.steps.length}`);

        // Clear and redraw proofs
        this.proofLayer.selectAll('*').remove();
        this.drawProofs(step.proofs);
    }

    drawProofs(proofs) {
        proofs.forEach(proof => {
            const x = proof.party === 'alice' ? 200 : 600;
            const y = 150 + proof.level * 70;
            const color = proof.party === 'alice' ? this.colors.alice : this.colors.bob;

            const group = this.proofLayer.append('g')
                .attr('class', `proof proof-${proof.id}`)
                .attr('transform', `translate(${x}, ${y})`)
                .attr('opacity', 0);

            // Main proof box
            const boxWidth = proof.expanded ? 160 : (proof.level === 0 ? 60 : 80 + proof.level * 20);
            const boxHeight = proof.expanded ? 120 : (30 + proof.level * 5);

            group.append('rect')
                .attr('x', -boxWidth / 2)
                .attr('y', -boxHeight / 2)
                .attr('width', boxWidth)
                .attr('height', boxHeight)
                .attr('fill', proof.isFixpoint ? this.colors.fixpoint : color)
                .attr('fill-opacity', proof.isFixpoint ? 0.3 : 0.15)
                .attr('stroke', proof.isFixpoint ? this.colors.fixpoint : color)
                .attr('stroke-width', proof.isFixpoint ? 3 : 2)
                .attr('rx', 6);

            // Proof label
            group.append('text')
                .attr('text-anchor', 'middle')
                .attr('dy', proof.expanded ? -40 : 5)
                .attr('fill', this.colors.text)
                .attr('font-size', '14px')
                .attr('font-weight', 'bold')
                .attr('font-family', "'JetBrains Mono', monospace")
                .text(proof.id);

            // Show contained proofs
            if (proof.contains.length > 0 && proof.expanded) {
                const containedText = proof.contains.join(', ');
                group.append('text')
                    .attr('text-anchor', 'middle')
                    .attr('dy', 0)
                    .attr('fill', this.colors.embedding)
                    .attr('font-size', '10px')
                    .attr('font-family', "'JetBrains Mono', monospace")
                    .text(`Contains:`);

                // Show nested structure
                proof.contains.forEach((c, i) => {
                    const row = Math.floor(i / 3);
                    const col = i % 3;
                    group.append('text')
                        .attr('x', (col - 1) * 45)
                        .attr('y', 20 + row * 18)
                        .attr('text-anchor', 'middle')
                        .attr('fill', this.colors.muted)
                        .attr('font-size', '9px')
                        .attr('font-family', "'JetBrains Mono', monospace")
                        .text(c);
                });
            } else if (proof.contains.length > 0) {
                // Compact contains indicator
                group.append('text')
                    .attr('text-anchor', 'middle')
                    .attr('dy', 20)
                    .attr('fill', this.colors.embedding)
                    .attr('font-size', '9px')
                    .text(`{${proof.contains.join(', ')}}`);
            }

            // Sent arrow
            if (proof.sentTo) {
                const arrowX = proof.party === 'alice' ? boxWidth / 2 + 20 : -boxWidth / 2 - 20;
                group.append('text')
                    .attr('x', arrowX)
                    .attr('text-anchor', 'middle')
                    .attr('fill', this.colors.muted)
                    .attr('font-size', '16px')
                    .text(proof.party === 'alice' ? '→' : '←');
            }

            // Fixpoint indicator
            if (proof.isFixpoint) {
                group.append('text')
                    .attr('y', proof.expanded ? 55 : boxHeight / 2 + 15)
                    .attr('text-anchor', 'middle')
                    .attr('fill', this.colors.fixpoint)
                    .attr('font-size', '10px')
                    .attr('font-weight', 'bold')
                    .text('✓ FIXPOINT');
            }

            // Fade in
            group.transition()
                .duration(500)
                .attr('opacity', 1);
        });
    }

    nextStep() {
        if (this.currentStep < this.steps.length - 1) {
            this.showStep(this.currentStep + 1);
        }
    }

    prevStep() {
        if (this.currentStep > 0) {
            this.showStep(this.currentStep - 1);
        }
    }

    toggleAutoPlay() {
        if (this.isAnimating) {
            this.stopAutoPlay();
        } else {
            this.startAutoPlay();
        }
    }

    startAutoPlay() {
        this.isAnimating = true;
        this.playText.text('⏸ Pause');
        this.playBtn.attr('fill', this.colors.bob).attr('fill-opacity', 0.2);

        const advance = () => {
            if (!this.isAnimating) return;

            if (this.currentStep < this.steps.length - 1) {
                this.nextStep();
                this.animationTimer = setTimeout(advance, 2000);
            } else {
                this.stopAutoPlay();
            }
        };

        this.animationTimer = setTimeout(advance, 2000);
    }

    stopAutoPlay() {
        this.isAnimating = false;
        this.playText.text('▶ Auto-play');
        this.playBtn.attr('fill', this.colors.alice).attr('fill-opacity', 0.2);

        if (this.animationTimer) {
            clearTimeout(this.animationTimer);
            this.animationTimer = null;
        }
    }

    reset() {
        this.stopAutoPlay();
        this.showStep(0);
    }
}

// =============================================================================
// Section 4: Phase Walkthrough
// =============================================================================

export class PhaseWalkthrough {
    /**
     * Interactive step-by-step walkthrough of the protocol phases:
     *
     * Phase 1: Commitment (C) - "I will attack if you agree"
     * Phase 2: Double (D) - "I know you've committed"
     * Phase 3: Triple (T) - "I know that you know I've committed"
     * Phase 4: Quaternary (Q) - Epistemic fixpoint achieved
     *
     * Features:
     * - Click-through navigation
     * - Auto-play mode
     * - Visual representation of epistemic depth
     * - Bilateral construction property highlight
     * - Detailed phase transition explanations
     * - Visual proof embedding diagram
     */
    constructor(container) {
        this.container = d3.select(container);
        this.width = 900;
        this.height = 700;
        this.svg = null;
        this.currentPhase = 0;
        this.isPlaying = false;
        this.playTimer = null;

        this.colors = {
            alice: '#58a6ff',
            bob: '#3fb950',
            phase1: '#58a6ff',
            phase2: '#a371f7',
            phase3: '#d29922',
            phase4: '#3fb950',
            text: '#f0f6fc',
            muted: '#8b949e',
            bg: '#0d1117',
            highlight: '#f0883e',
            embedding: '#a371f7'
        };

        this.phases = [
            {
                id: 'C',
                name: 'Commitment',
                formula: 'C_X = Sign_X("I will attack at dawn if you agree")',
                epistemicDepth: 0,
                aliceThinks: 'I want to coordinate.',
                bobThinks: 'I want to coordinate.',
                status: 'Unilateral intent only',
                action: 'Each floods C continuously',
                explanation: 'Each party generates a signed commitment and begins flooding it. At this stage, there is no knowledge of the other party.',
                transition: 'Upon receiving C_Y, each party advances to Phase 2',
                embeds: [],
                bilateralProperty: false
            },
            {
                id: 'D',
                name: 'Double Proof',
                formula: 'D_X = Sign_X(C_X ∥ C_Y ∥ "Both parties committed")',
                epistemicDepth: 1,
                aliceThinks: 'I know Bob committed.',
                bobThinks: 'I know Alice committed.',
                status: 'Mutual commitment confirmed',
                action: 'Each floods D after receiving other\'s C',
                explanation: 'Upon receiving the other party\'s commitment, each party constructs D by signing BOTH commitments together. This creates first-order knowledge: "I know you committed."',
                transition: 'Upon receiving D_Y, each party advances to Phase 3',
                embeds: ['C_A', 'C_B'],
                bilateralProperty: false
            },
            {
                id: 'T',
                name: 'Triple Proof',
                formula: 'T_X = Sign_X(D_X ∥ D_Y ∥ "Both have double proofs")',
                epistemicDepth: 2,
                aliceThinks: 'I know Bob knows I committed.',
                bobThinks: 'I know Alice knows I committed.',
                status: 'Second-order knowledge',
                action: 'Each floods T after receiving other\'s D',
                explanation: 'Upon receiving the other party\'s double proof, each party constructs T by signing BOTH double proofs together. Critically: receiving D_Y gives you the embedded commitments for FREE. This creates second-order knowledge.',
                transition: 'Upon receiving T_Y, each party advances to Phase 4',
                embeds: ['D_A', 'D_B', 'C_A', 'C_B'],
                bilateralProperty: false
            },
            {
                id: 'Q',
                name: 'Quaternary Proof (Fixpoint)',
                formula: 'Q_X = Sign_X(T_X ∥ T_Y ∥ "Fixpoint achieved")',
                epistemicDepth: 'ω',
                aliceThinks: 'I know that Bob knows that I know that Bob knows... ∞',
                bobThinks: 'I know that Alice knows that I know that Alice knows... ∞',
                status: 'EPISTEMIC FIXPOINT',
                action: 'ATTACK!',
                explanation: 'This is the bilateral construction property: Q_A exists → contains T_B → Bob had D_A → Bob can construct T_B → Bob can construct Q_B. Neither half can exist without the other being constructible. The knot is tied.',
                transition: 'Common knowledge achieved. Coordination guaranteed.',
                embeds: ['T_A', 'T_B', 'D_A', 'D_B', 'C_A', 'C_B'],
                bilateralProperty: true,
                isFixpoint: true
            }
        ];
    }

    init() {
        this.container.html('');

        this.svg = this.container.append('svg')
            .attr('viewBox', `0 0 ${this.width} ${this.height}`)
            .attr('preserveAspectRatio', 'xMidYMid meet')
            .style('width', '100%')
            .style('max-width', '800px')
            .style('height', 'auto');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', this.colors.bg)
            .attr('rx', 12);

        this.drawTitle();
        this.drawPhaseIndicators();
        this.phaseContent = this.svg.append('g')
            .attr('class', 'phase-content')
            .attr('transform', 'translate(0, 100)');
        this.drawControls();
        this.drawBilateralProperty();

        this.showPhase(0);
    }

    drawTitle() {
        this.svg.append('text')
            .attr('x', this.width / 2)
            .attr('y', 30)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '18px')
            .attr('font-weight', 'bold')
            .text('Protocol Phase Walkthrough');

        this.svg.append('text')
            .attr('x', this.width / 2)
            .attr('y', 50)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '12px')
            .text('From commitment to epistemic fixpoint');
    }

    drawPhaseIndicators() {
        const indicatorY = 75;
        const indicatorGroup = this.svg.append('g')
            .attr('class', 'phase-indicators');

        this.phases.forEach((phase, i) => {
            const x = 150 + i * 150;
            const color = this.colors[`phase${i + 1}`];

            // Circle
            indicatorGroup.append('circle')
                .attr('class', `indicator indicator-${i}`)
                .attr('cx', x)
                .attr('cy', indicatorY)
                .attr('r', 20)
                .attr('fill', color)
                .attr('fill-opacity', 0.2)
                .attr('stroke', color)
                .attr('stroke-width', 2)
                .style('cursor', 'pointer')
                .on('click', () => this.showPhase(i));

            // Phase letter
            indicatorGroup.append('text')
                .attr('x', x)
                .attr('y', indicatorY + 5)
                .attr('text-anchor', 'middle')
                .attr('fill', color)
                .attr('font-size', '14px')
                .attr('font-weight', 'bold')
                .attr('font-family', "'JetBrains Mono', monospace")
                .text(phase.id)
                .style('pointer-events', 'none');

            // Connector line
            if (i < this.phases.length - 1) {
                indicatorGroup.append('line')
                    .attr('x1', x + 25)
                    .attr('y1', indicatorY)
                    .attr('x2', x + 125)
                    .attr('y2', indicatorY)
                    .attr('stroke', this.colors.muted)
                    .attr('stroke-width', 2)
                    .attr('stroke-dasharray', '4,4');
            }
        });
    }

    drawControls() {
        const controlY = this.height - 40;

        // Previous button
        this.svg.append('rect')
            .attr('class', 'control-btn')
            .attr('x', 250)
            .attr('y', controlY - 15)
            .attr('width', 80)
            .attr('height', 30)
            .attr('fill', '#21262d')
            .attr('stroke', '#30363d')
            .attr('rx', 4)
            .style('cursor', 'pointer')
            .on('click', () => this.prevPhase());

        this.svg.append('text')
            .attr('x', 290)
            .attr('y', controlY + 4)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .text('← Prev')
            .style('pointer-events', 'none');

        // Auto-play button
        this.playButton = this.svg.append('rect')
            .attr('class', 'play-btn')
            .attr('x', 350)
            .attr('y', controlY - 15)
            .attr('width', 100)
            .attr('height', 30)
            .attr('fill', this.colors.phase1)
            .attr('fill-opacity', 0.2)
            .attr('stroke', this.colors.phase1)
            .attr('rx', 4)
            .style('cursor', 'pointer')
            .on('click', () => this.togglePlay());

        this.playButtonText = this.svg.append('text')
            .attr('x', 400)
            .attr('y', controlY + 4)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.phase1)
            .attr('font-size', '12px')
            .text('▶ Auto-play')
            .style('pointer-events', 'none');

        // Next button
        this.svg.append('rect')
            .attr('class', 'control-btn')
            .attr('x', 470)
            .attr('y', controlY - 15)
            .attr('width', 80)
            .attr('height', 30)
            .attr('fill', '#21262d')
            .attr('stroke', '#30363d')
            .attr('rx', 4)
            .style('cursor', 'pointer')
            .on('click', () => this.nextPhase());

        this.svg.append('text')
            .attr('x', 510)
            .attr('y', controlY + 4)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .text('Next →')
            .style('pointer-events', 'none');
    }

    drawBilateralProperty() {
        // Box at bottom showing the bilateral construction property
        const boxY = this.height - 100;

        this.bilateralBox = this.svg.append('g')
            .attr('class', 'bilateral-box')
            .attr('transform', `translate(${this.width / 2}, ${boxY})`)
            .attr('opacity', 0);

        this.bilateralBox.append('rect')
            .attr('x', -350)
            .attr('y', -20)
            .attr('width', 700)
            .attr('height', 45)
            .attr('fill', this.colors.highlight)
            .attr('fill-opacity', 0.1)
            .attr('stroke', this.colors.highlight)
            .attr('stroke-width', 2)
            .attr('rx', 8);

        this.bilateralBox.append('text')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.highlight)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('THE BILATERAL CONSTRUCTION PROPERTY');

        this.bilateralBox.append('text')
            .attr('y', 18)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '11px')
            .text('Q_A exists → contains T_B → Bob had D_A → Bob can construct Q_B. Neither can exist without the other.');
    }

    showPhase(phaseIndex) {
        this.currentPhase = Math.max(0, Math.min(phaseIndex, this.phases.length - 1));
        const phase = this.phases[this.currentPhase];
        const color = this.colors[`phase${this.currentPhase + 1}`];

        // Update indicators
        this.svg.selectAll('.indicator')
            .transition()
            .duration(300)
            .attr('fill-opacity', (d, i) => i === this.currentPhase ? 0.8 : 0.2)
            .attr('stroke-width', (d, i) => i === this.currentPhase ? 3 : 2);

        // Clear and redraw content
        this.phaseContent.selectAll('*').remove();

        // Phase name and formula
        this.phaseContent.append('text')
            .attr('x', this.width / 2)
            .attr('y', 30)
            .attr('text-anchor', 'middle')
            .attr('fill', color)
            .attr('font-size', '20px')
            .attr('font-weight', 'bold')
            .text(`Phase ${this.currentPhase + 1}: ${phase.name}`);

        // Formula box
        this.phaseContent.append('rect')
            .attr('x', 50)
            .attr('y', 55)
            .attr('width', 800)
            .attr('height', 45)
            .attr('fill', '#161b22')
            .attr('stroke', color)
            .attr('stroke-width', 2)
            .attr('rx', 6);

        this.phaseContent.append('text')
            .attr('x', this.width / 2)
            .attr('y', 83)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '13px')
            .attr('font-family', "'JetBrains Mono', monospace")
            .text(phase.formula);

        // Two columns: Alice and Bob
        this.drawPartyColumn(170, phase, 'alice', this.colors.alice);
        this.drawPartyColumn(730, phase, 'bob', this.colors.bob);

        // Explanation section
        this.drawExplanationSection(phase, color);

        // Visual proof embedding diagram
        if (phase.embeds.length > 0) {
            this.drawProofEmbedding(phase, color);
        }

        // Transition explanation
        this.phaseContent.append('text')
            .attr('x', this.width / 2)
            .attr('y', 500)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '11px')
            .attr('font-style', 'italic')
            .text(`→ ${phase.transition}`);

        // Show bilateral property on phase 4
        this.bilateralBox.transition()
            .duration(500)
            .attr('opacity', phase.bilateralProperty ? 1 : 0);
    }

    drawExplanationSection(phase, color) {
        // Explanation box
        const explainY = 270;
        const boxHeight = 70;

        this.phaseContent.append('rect')
            .attr('x', 50)
            .attr('y', explainY)
            .attr('width', 800)
            .attr('height', boxHeight)
            .attr('fill', color)
            .attr('fill-opacity', 0.05)
            .attr('stroke', color)
            .attr('stroke-width', 1)
            .attr('stroke-opacity', 0.3)
            .attr('rx', 6);

        // Explanation title
        this.phaseContent.append('text')
            .attr('x', 65)
            .attr('y', explainY + 20)
            .attr('fill', color)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('What happens:');

        // Explanation text (word-wrapped)
        this.wrapText(
            phase.explanation,
            65,
            explainY + 40,
            770,
            this.colors.text,
            11
        );

        // Status and action boxes
        const statusY = explainY + boxHeight + 15;

        this.phaseContent.append('rect')
            .attr('x', 50)
            .attr('y', statusY)
            .attr('width', 390)
            .attr('height', 35)
            .attr('fill', '#161b22')
            .attr('stroke', this.colors.muted)
            .attr('stroke-width', 1)
            .attr('rx', 4);

        this.phaseContent.append('text')
            .attr('x', 245)
            .attr('y', statusY + 12)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '9px')
            .text('STATUS');

        this.phaseContent.append('text')
            .attr('x', 245)
            .attr('y', statusY + 26)
            .attr('text-anchor', 'middle')
            .attr('fill', phase.isFixpoint ? this.colors.highlight : this.colors.text)
            .attr('font-size', '12px')
            .attr('font-weight', phase.isFixpoint ? 'bold' : 'normal')
            .text(phase.status);

        this.phaseContent.append('rect')
            .attr('x', 460)
            .attr('y', statusY)
            .attr('width', 390)
            .attr('height', 35)
            .attr('fill', '#161b22')
            .attr('stroke', this.colors.muted)
            .attr('stroke-width', 1)
            .attr('rx', 4);

        this.phaseContent.append('text')
            .attr('x', 655)
            .attr('y', statusY + 12)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '9px')
            .text('ACTION');

        this.phaseContent.append('text')
            .attr('x', 655)
            .attr('y', statusY + 26)
            .attr('text-anchor', 'middle')
            .attr('fill', phase.isFixpoint ? this.colors.phase4 : this.colors.text)
            .attr('font-size', '12px')
            .text(phase.action);

        // Epistemic depth
        this.phaseContent.append('text')
            .attr('x', this.width / 2)
            .attr('y', statusY + 55)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.embedding)
            .attr('font-size', '11px')
            .attr('font-weight', 'bold')
            .text(`Epistemic Depth: ${phase.epistemicDepth}${phase.isFixpoint ? ' (FIXPOINT)' : ''}`);
    }

    drawProofEmbedding(phase, color) {
        // Visual diagram showing what's embedded in this proof
        const embedY = 420;

        this.phaseContent.append('text')
            .attr('x', this.width / 2)
            .attr('y', embedY)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.embedding)
            .attr('font-size', '11px')
            .attr('font-weight', 'bold')
            .text(`${phase.id} contains:`);

        // Draw embedded proofs as nested boxes
        const startX = this.width / 2 - (phase.embeds.length * 60) / 2;

        phase.embeds.forEach((embed, i) => {
            const x = startX + i * 60;
            const y = embedY + 15;

            this.phaseContent.append('rect')
                .attr('x', x)
                .attr('y', y)
                .attr('width', 50)
                .attr('height', 30)
                .attr('fill', this.colors.embedding)
                .attr('fill-opacity', 0.1)
                .attr('stroke', this.colors.embedding)
                .attr('stroke-width', 1)
                .attr('rx', 4);

            this.phaseContent.append('text')
                .attr('x', x + 25)
                .attr('y', y + 19)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.embedding)
                .attr('font-size', '10px')
                .attr('font-family', "'JetBrains Mono', monospace")
                .text(embed);
        });

        // Arrow showing embedding
        if (phase.embeds.length > 0) {
            this.phaseContent.append('text')
                .attr('x', this.width / 2)
                .attr('y', embedY + 63)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.muted)
                .attr('font-size', '10px')
                .attr('font-style', 'italic')
                .text('Receiving higher-level proof gives you all nested proofs for FREE');
        }
    }

    wrapText(text, x, y, maxWidth, fill, fontSize) {
        const words = text.split(' ');
        let line = '';
        let lineNum = 0;
        const lineHeight = fontSize * 1.4;

        words.forEach(word => {
            const testLine = line + word + ' ';
            const testWidth = testLine.length * fontSize * 0.5; // Rough estimate

            if (testWidth > maxWidth && line !== '') {
                this.phaseContent.append('text')
                    .attr('x', x)
                    .attr('y', y + lineNum * lineHeight)
                    .attr('fill', fill)
                    .attr('font-size', `${fontSize}px`)
                    .text(line.trim());
                line = word + ' ';
                lineNum++;
            } else {
                line = testLine;
            }
        });

        // Last line
        this.phaseContent.append('text')
            .attr('x', x)
            .attr('y', y + lineNum * lineHeight)
            .attr('fill', fill)
            .attr('font-size', `${fontSize}px`)
            .text(line.trim());
    }

    drawPartyColumn(x, phase, party, color) {
        const colGroup = this.phaseContent.append('g')
            .attr('transform', `translate(${x}, 110)`);

        // Party label
        colGroup.append('circle')
            .attr('r', 25)
            .attr('fill', color)
            .attr('fill-opacity', 0.2)
            .attr('stroke', color)
            .attr('stroke-width', 2);

        colGroup.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', 5)
            .attr('fill', color)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text(party === 'alice' ? 'A' : 'B');

        // Thought bubble
        const thinks = party === 'alice' ? phase.aliceThinks : phase.bobThinks;
        colGroup.append('rect')
            .attr('x', -100)
            .attr('y', 40)
            .attr('width', 200)
            .attr('height', 60)
            .attr('fill', '#161b22')
            .attr('stroke', color)
            .attr('stroke-width', 1)
            .attr('rx', 8);

        // Split text if too long
        const words = thinks.split(' ');
        let lines = [];
        let currentLine = '';
        words.forEach(word => {
            if ((currentLine + ' ' + word).length > 25) {
                lines.push(currentLine);
                currentLine = word;
            } else {
                currentLine = currentLine ? currentLine + ' ' + word : word;
            }
        });
        if (currentLine) lines.push(currentLine);

        lines.forEach((line, i) => {
            colGroup.append('text')
                .attr('x', 0)
                .attr('y', 60 + i * 16)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.text)
                .attr('font-size', '11px')
                .attr('font-style', 'italic')
                .text(`"${line}"`);
        });
    }

    nextPhase() {
        if (this.currentPhase < this.phases.length - 1) {
            this.showPhase(this.currentPhase + 1);
        }
    }

    prevPhase() {
        if (this.currentPhase > 0) {
            this.showPhase(this.currentPhase - 1);
        }
    }

    togglePlay() {
        if (this.isPlaying) {
            this.stopPlay();
        } else {
            this.startPlay();
        }
    }

    startPlay() {
        this.isPlaying = true;
        this.playButtonText.text('⏸ Pause');
        this.playButton.attr('fill', this.colors.phase4);

        const advance = () => {
            if (!this.isPlaying) return;

            if (this.currentPhase < this.phases.length - 1) {
                this.nextPhase();
                this.playTimer = setTimeout(advance, 3000);
            } else {
                this.stopPlay();
            }
        };

        this.playTimer = setTimeout(advance, 3000);
    }

    stopPlay() {
        this.isPlaying = false;
        this.playButtonText.text('▶ Auto-play');
        this.playButton.attr('fill', this.colors.phase1);

        if (this.playTimer) {
            clearTimeout(this.playTimer);
            this.playTimer = null;
        }
    }

    reset() {
        this.stopPlay();
        this.showPhase(0);
    }
}

// =============================================================================
// Updated Explainer Controller (with Sections 3-4)
// =============================================================================

// Extend ExplainerController to include Sections 3-4
ExplainerController.prototype.initSolutionSections = function() {
    const proofMergingContainer = document.getElementById('proof-merging');
    const phaseWalkthroughContainer = document.getElementById('phase-walkthrough');

    if (proofMergingContainer) {
        this.proofMerging = new ProofMergingAnimation(proofMergingContainer);
        this.proofMerging.init();
        this.sections.push(this.proofMerging);
    }

    if (phaseWalkthroughContainer) {
        this.phaseWalkthrough = new PhaseWalkthrough(phaseWalkthroughContainer);
        this.phaseWalkthrough.init();
        this.sections.push(this.phaseWalkthrough);
    }
};
