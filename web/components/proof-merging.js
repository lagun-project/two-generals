/**
 * TGP Web Visualizer - Proof Merging Component
 *
 * D3.js-powered visualization showing how proofs embed at each level
 * of the TGP protocol, leading to the bilateral construction fixpoint.
 *
 * Key Concept: Each proof level embeds all previous proofs:
 * - C: Standalone commitment
 * - D = Sign(C_A + C_B): Contains both commitments
 * - T = Sign(D_A + D_B): Contains both doubles (and thus all C's)
 * - Q = Sign(T_A + T_B): Contains everything (epistemic fixpoint)
 *
 * The self-certifying property: receiving Q gives you all proofs for free!
 */

import * as d3 from 'd3';
import { Colors, Timing, Phase, phaseName } from './types.js';

/**
 * Represents a proof artifact at a specific level.
 */
class ProofNode {
    constructor(id, party, level, contains = []) {
        this.id = id;
        this.party = party;      // 'alice' or 'bob'
        this.level = level;      // 0=C, 1=D, 2=T, 3=Q
        this.contains = contains; // IDs of embedded proofs
        this.isFixpoint = level === 3;
    }
}

export class ProofMergingVisualizer {
    /**
     * Create a new proof merging visualizer.
     * @param {string|HTMLElement} container - Container selector or element
     */
    constructor(container) {
        this.container = typeof container === 'string'
            ? d3.select(container)
            : d3.select(container);

        this.width = 800;
        this.height = 500;
        this.margin = { top: 50, right: 40, bottom: 60, left: 40 };

        // Animation state
        this.currentStep = 0;
        this.isAnimating = false;
        this.animationId = null;

        // Colors
        this.colors = {
            alice: Colors.alice,
            bob: Colors.bob,
            commitment: Colors.commitment,
            double: Colors.double,
            triple: Colors.triple,
            quad: Colors.quad,
            text: Colors.text,
            muted: Colors.muted,
            bg: Colors.bgDark,
            embedding: '#a371f7'
        };

        // Proof level colors
        this.levelColors = [
            this.colors.commitment, // C
            this.colors.double,     // D
            this.colors.triple,     // T
            this.colors.quad        // Q
        ];

        // Define animation steps
        this.steps = this.defineSteps();

        // SVG groups
        this.svg = null;
        this.proofGroup = null;
        this.arrowGroup = null;
        this.labelGroup = null;

        this.init();
    }

    /**
     * Define the animation steps showing proof evolution.
     */
    defineSteps() {
        return [
            {
                title: 'Initial State',
                description: 'Alice and Bob each generate their signed commitment.',
                proofs: [
                    new ProofNode('C_A', 'alice', 0),
                    new ProofNode('C_B', 'bob', 0)
                ],
                arrows: []
            },
            {
                title: 'Commitments Exchanged',
                description: 'Each party receives the other\'s commitment via flooding.',
                proofs: [
                    new ProofNode('C_A', 'alice', 0),
                    new ProofNode('C_B', 'bob', 0)
                ],
                arrows: [
                    { from: 'C_A', to: 'bob', label: 'flood' },
                    { from: 'C_B', to: 'alice', label: 'flood' }
                ]
            },
            {
                title: 'Double Proofs Created',
                description: 'Each party creates D by signing both commitments together.',
                proofs: [
                    new ProofNode('D_A', 'alice', 1, ['C_A', 'C_B']),
                    new ProofNode('D_B', 'bob', 1, ['C_A', 'C_B'])
                ],
                arrows: [],
                highlight: 'embedding'
            },
            {
                title: 'Double Proofs Exchanged',
                description: 'Each party receives the other\'s double proof.',
                proofs: [
                    new ProofNode('D_A', 'alice', 1, ['C_A', 'C_B']),
                    new ProofNode('D_B', 'bob', 1, ['C_A', 'C_B'])
                ],
                arrows: [
                    { from: 'D_A', to: 'bob', label: 'flood' },
                    { from: 'D_B', to: 'alice', label: 'flood' }
                ]
            },
            {
                title: 'Triple Proofs Created',
                description: 'Each party creates T by signing both double proofs.',
                proofs: [
                    new ProofNode('T_A', 'alice', 2, ['D_A', 'D_B']),
                    new ProofNode('T_B', 'bob', 2, ['D_A', 'D_B'])
                ],
                arrows: [],
                highlight: 'embedding'
            },
            {
                title: 'Triple Proofs Exchanged',
                description: 'Each party receives the other\'s triple proof.',
                proofs: [
                    new ProofNode('T_A', 'alice', 2, ['D_A', 'D_B']),
                    new ProofNode('T_B', 'bob', 2, ['D_A', 'D_B'])
                ],
                arrows: [
                    { from: 'T_A', to: 'bob', label: 'flood' },
                    { from: 'T_B', to: 'alice', label: 'flood' }
                ]
            },
            {
                title: 'Quaternary Proofs - FIXPOINT!',
                description: 'Both parties construct Q. Bilateral property: Q_A ↔ Q_B',
                proofs: [
                    new ProofNode('Q_A', 'alice', 3, ['T_A', 'T_B']),
                    new ProofNode('Q_B', 'bob', 3, ['T_A', 'T_B'])
                ],
                arrows: [],
                highlight: 'fixpoint'
            },
            {
                title: 'The Self-Certifying Property',
                description: 'Q contains all previous proofs. Having Q proves common knowledge.',
                proofs: [
                    new ProofNode('Q_A', 'alice', 3, ['T_A', 'T_B', 'D_A', 'D_B', 'C_A', 'C_B']),
                    new ProofNode('Q_B', 'bob', 3, ['T_A', 'T_B', 'D_A', 'D_B', 'C_A', 'C_B'])
                ],
                arrows: [],
                highlight: 'self-certifying',
                expanded: true
            }
        ];
    }

    /**
     * Initialize the visualization.
     */
    init() {
        this.container.selectAll('*').remove();

        this.svg = this.container.append('svg')
            .attr('viewBox', `0 0 ${this.width} ${this.height}`)
            .attr('class', 'proof-merging-svg')
            .attr('role', 'graphics-document')
            .attr('aria-label', 'Proof embedding and merging visualization');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', this.colors.bg)
            .attr('rx', 8);

        // Defs for gradients and markers
        this.setupDefs();

        // Title area
        this.titleGroup = this.svg.append('g')
            .attr('class', 'title')
            .attr('transform', 'translate(400, 30)');

        this.titleGroup.append('text')
            .attr('class', 'step-title')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '18px')
            .attr('font-weight', 'bold')
            .text('Proof Merging Animation');

        this.titleGroup.append('text')
            .attr('class', 'step-description')
            .attr('y', 25)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '13px')
            .text('Watch how proofs embed into each other');

        this.titleGroup.append('text')
            .attr('class', 'step-counter')
            .attr('y', 50)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '11px')
            .text(`Step 1 of ${this.steps.length}`);

        // Party zones
        this.drawPartyZones();

        // Create layer groups
        this.arrowGroup = this.svg.append('g').attr('class', 'arrows');
        this.proofGroup = this.svg.append('g').attr('class', 'proofs');
        this.labelGroup = this.svg.append('g').attr('class', 'labels');

        // Controls
        this.drawControls();

        // Show initial step
        this.showStep(0);
    }

    /**
     * Setup SVG defs (gradients, markers, filters).
     */
    setupDefs() {
        const defs = this.svg.append('defs');

        // Arrow markers for each party
        defs.append('marker')
            .attr('id', 'arrow-alice')
            .attr('viewBox', '0 0 10 10')
            .attr('refX', 8)
            .attr('refY', 5)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M 0 0 L 10 5 L 0 10 Z')
            .attr('fill', this.colors.alice);

        defs.append('marker')
            .attr('id', 'arrow-bob')
            .attr('viewBox', '0 0 10 10')
            .attr('refX', 8)
            .attr('refY', 5)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M 0 0 L 10 5 L 0 10 Z')
            .attr('fill', this.colors.bob);

        // Glow filter for fixpoint
        const glowFilter = defs.append('filter')
            .attr('id', 'fixpoint-glow')
            .attr('x', '-50%')
            .attr('y', '-50%')
            .attr('width', '200%')
            .attr('height', '200%');

        glowFilter.append('feGaussianBlur')
            .attr('stdDeviation', '4')
            .attr('result', 'blur');

        const feMerge = glowFilter.append('feMerge');
        feMerge.append('feMergeNode').attr('in', 'blur');
        feMerge.append('feMergeNode').attr('in', 'SourceGraphic');
    }

    /**
     * Draw the party zones (Alice left, Bob right).
     */
    drawPartyZones() {
        // Alice zone
        this.svg.append('rect')
            .attr('x', 30)
            .attr('y', 80)
            .attr('width', 340)
            .attr('height', 300)
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

        // Bob zone
        this.svg.append('rect')
            .attr('x', 430)
            .attr('y', 80)
            .attr('width', 340)
            .attr('height', 300)
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
            .attr('y', 200)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '10px')
            .text('Lossy Channel');

        this.svg.append('line')
            .attr('x1', 375)
            .attr('y1', 210)
            .attr('x2', 375)
            .attr('y2', 340)
            .attr('stroke', this.colors.muted)
            .attr('stroke-dasharray', '4,4')
            .attr('stroke-opacity', 0.5);

        this.svg.append('line')
            .attr('x1', 425)
            .attr('y1', 210)
            .attr('x2', 425)
            .attr('y2', 340)
            .attr('stroke', this.colors.muted)
            .attr('stroke-dasharray', '4,4')
            .attr('stroke-opacity', 0.5);
    }

    /**
     * Draw navigation controls.
     */
    drawControls() {
        const controlY = this.height - 45;
        const controlGroup = this.svg.append('g').attr('class', 'controls');

        // Previous button
        controlGroup.append('rect')
            .attr('x', 260)
            .attr('y', controlY)
            .attr('width', 70)
            .attr('height', 32)
            .attr('fill', '#21262d')
            .attr('stroke', '#30363d')
            .attr('rx', 6)
            .style('cursor', 'pointer')
            .on('click', () => this.prevStep());

        controlGroup.append('text')
            .attr('x', 295)
            .attr('y', controlY + 20)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .text('← Prev')
            .style('pointer-events', 'none');

        // Play/Pause button
        this.playBtn = controlGroup.append('rect')
            .attr('x', 345)
            .attr('y', controlY)
            .attr('width', 110)
            .attr('height', 32)
            .attr('fill', this.colors.alice)
            .attr('fill-opacity', 0.2)
            .attr('stroke', this.colors.alice)
            .attr('rx', 6)
            .style('cursor', 'pointer')
            .on('click', () => this.toggleAutoPlay());

        this.playText = controlGroup.append('text')
            .attr('x', 400)
            .attr('y', controlY + 20)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.alice)
            .attr('font-size', '12px')
            .text('▶ Auto-play')
            .style('pointer-events', 'none');

        // Next button
        controlGroup.append('rect')
            .attr('x', 470)
            .attr('y', controlY)
            .attr('width', 70)
            .attr('height', 32)
            .attr('fill', '#21262d')
            .attr('stroke', '#30363d')
            .attr('rx', 6)
            .style('cursor', 'pointer')
            .on('click', () => this.nextStep());

        controlGroup.append('text')
            .attr('x', 505)
            .attr('y', controlY + 20)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .text('Next →')
            .style('pointer-events', 'none');
    }

    /**
     * Show a specific step in the animation.
     * @param {number} stepIndex - Step index to show
     */
    showStep(stepIndex) {
        this.currentStep = Math.max(0, Math.min(stepIndex, this.steps.length - 1));
        const step = this.steps[this.currentStep];

        // Update title
        this.titleGroup.select('.step-title')
            .transition()
            .duration(200)
            .attr('opacity', 0)
            .transition()
            .duration(200)
            .text(step.title)
            .attr('opacity', 1);

        this.titleGroup.select('.step-description')
            .transition()
            .duration(200)
            .text(step.description);

        this.titleGroup.select('.step-counter')
            .text(`Step ${this.currentStep + 1} of ${this.steps.length}`);

        // Clear and redraw
        this.arrowGroup.selectAll('*').remove();
        this.proofGroup.selectAll('*').remove();
        this.labelGroup.selectAll('*').remove();

        // Draw proofs
        step.proofs.forEach(proof => this.drawProof(proof, step.expanded));

        // Draw arrows
        step.arrows.forEach(arrow => this.drawArrow(arrow));
    }

    /**
     * Draw a proof node.
     * @param {ProofNode} proof - Proof to draw
     * @param {boolean} expanded - Whether to show expanded view
     */
    drawProof(proof, expanded = false) {
        const x = proof.party === 'alice' ? 200 : 600;
        const y = 140 + proof.level * 65;
        const color = this.levelColors[proof.level];
        const partyColor = proof.party === 'alice' ? this.colors.alice : this.colors.bob;

        // Calculate box size based on content
        const boxWidth = expanded ? 150 : (60 + proof.level * 20);
        const boxHeight = expanded ? (30 + proof.contains.length * 12) : (30 + proof.level * 4);

        const group = this.proofGroup.append('g')
            .attr('class', `proof proof-${proof.id}`)
            .attr('transform', `translate(${x}, ${y})`)
            .attr('opacity', 0);

        // Main box
        group.append('rect')
            .attr('x', -boxWidth / 2)
            .attr('y', -boxHeight / 2)
            .attr('width', boxWidth)
            .attr('height', boxHeight)
            .attr('fill', color)
            .attr('fill-opacity', proof.isFixpoint ? 0.3 : 0.15)
            .attr('stroke', color)
            .attr('stroke-width', proof.isFixpoint ? 3 : 2)
            .attr('rx', 6)
            .attr('filter', proof.isFixpoint ? 'url(#fixpoint-glow)' : null);

        // Proof ID label
        group.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', expanded ? -boxHeight / 2 + 18 : 5)
            .attr('fill', this.colors.text)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .attr('font-family', 'monospace')
            .text(proof.id);

        // Show contained proofs
        if (proof.contains.length > 0) {
            if (expanded) {
                // Detailed view
                group.append('text')
                    .attr('text-anchor', 'middle')
                    .attr('dy', -boxHeight / 2 + 35)
                    .attr('fill', this.colors.embedding)
                    .attr('font-size', '10px')
                    .text('Contains:');

                proof.contains.forEach((contained, i) => {
                    const row = Math.floor(i / 2);
                    const col = i % 2;
                    group.append('text')
                        .attr('x', (col - 0.5) * 50)
                        .attr('y', -boxHeight / 2 + 52 + row * 14)
                        .attr('text-anchor', 'middle')
                        .attr('fill', this.colors.muted)
                        .attr('font-size', '9px')
                        .attr('font-family', 'monospace')
                        .text(contained);
                });
            } else {
                // Compact view
                group.append('text')
                    .attr('text-anchor', 'middle')
                    .attr('dy', 22)
                    .attr('fill', this.colors.embedding)
                    .attr('font-size', '9px')
                    .text(`{${proof.contains.join(', ')}}`);
            }
        }

        // Fixpoint indicator
        if (proof.isFixpoint) {
            group.append('text')
                .attr('y', boxHeight / 2 + 18)
                .attr('text-anchor', 'middle')
                .attr('fill', color)
                .attr('font-size', '10px')
                .attr('font-weight', 'bold')
                .text('✓ FIXPOINT');
        }

        // Fade in
        group.transition()
            .duration(Timing.proof)
            .attr('opacity', 1);
    }

    /**
     * Draw an arrow between proofs or to a party.
     * @param {object} arrow - Arrow definition
     */
    drawArrow(arrow) {
        const fromProof = arrow.from;
        const toParty = arrow.to;

        // Calculate positions
        const fromX = fromProof.startsWith('C_A') || fromProof.startsWith('D_A') || fromProof.startsWith('T_A') || fromProof.startsWith('Q_A')
            ? 250 : 550;
        const toX = toParty === 'alice' ? 150 : 650;
        const y = 160 + (fromProof.charAt(0) === 'C' ? 0 : fromProof.charAt(0) === 'D' ? 65 : fromProof.charAt(0) === 'T' ? 130 : 195);

        const marker = toParty === 'alice' ? 'url(#arrow-bob)' : 'url(#arrow-alice)';
        const color = toParty === 'alice' ? this.colors.bob : this.colors.alice;

        const arrow_ = this.arrowGroup.append('line')
            .attr('x1', fromX)
            .attr('y1', y)
            .attr('x2', fromX)
            .attr('y2', y)
            .attr('stroke', color)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '4,4')
            .attr('marker-end', marker);

        arrow_.transition()
            .duration(Timing.proof)
            .attr('x2', toX);
    }

    /**
     * Step to the next step.
     * @returns {boolean} True if there are more steps
     */
    nextStep() {
        if (this.currentStep < this.steps.length - 1) {
            this.showStep(this.currentStep + 1);
            return true;
        }
        return false;
    }

    /**
     * Step to the previous step.
     */
    prevStep() {
        if (this.currentStep > 0) {
            this.showStep(this.currentStep - 1);
        }
    }

    /**
     * Toggle auto-play mode.
     */
    toggleAutoPlay() {
        if (this.isAnimating) {
            this.stopAutoPlay();
        } else {
            this.startAutoPlay();
        }
    }

    /**
     * Start auto-play mode.
     */
    startAutoPlay() {
        this.isAnimating = true;
        this.playText.text('⏸ Pause');
        this.playBtn.attr('fill', this.colors.bob).attr('fill-opacity', 0.2);

        const advance = () => {
            if (!this.isAnimating) return;

            if (this.nextStep()) {
                this.animationId = setTimeout(advance, 2000);
            } else {
                this.stopAutoPlay();
            }
        };

        this.animationId = setTimeout(advance, 2000);
    }

    /**
     * Stop auto-play mode.
     */
    stopAutoPlay() {
        this.isAnimating = false;
        this.playText.text('▶ Auto-play');
        this.playBtn.attr('fill', this.colors.alice).attr('fill-opacity', 0.2);

        if (this.animationId) {
            clearTimeout(this.animationId);
            this.animationId = null;
        }
    }

    /**
     * Reset to initial state.
     */
    reset() {
        this.stopAutoPlay();
        this.showStep(0);
    }

    /**
     * Clean up resources.
     */
    destroy() {
        this.stopAutoPlay();
        this.container.selectAll('*').remove();
    }
}

/**
 * Factory function to create the visualizer with controls.
 * @param {string} containerId - Container element ID
 * @returns {object} Visualizer instance and control methods
 */
export function createProofMergingDemo(containerId) {
    const container = document.getElementById(containerId);
    if (!container) {
        console.error(`Container not found: ${containerId}`);
        return null;
    }

    const visualizer = new ProofMergingVisualizer(container);

    return {
        visualizer,
        nextStep: () => visualizer.nextStep(),
        prevStep: () => visualizer.prevStep(),
        toggleAutoPlay: () => visualizer.toggleAutoPlay(),
        reset: () => visualizer.reset(),
        destroy: () => visualizer.destroy()
    };
}
