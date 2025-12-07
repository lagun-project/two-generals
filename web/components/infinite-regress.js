/**
 * TGP Web Visualizer - Infinite Regress Component
 *
 * D3.js-powered visualization showing the infinite ACK chain problem.
 * Demonstrates why traditional acknowledgment protocols fail:
 * MSG → ACK → ACK-of-ACK → ACK-of-ACK-of-ACK → ...
 *
 * Features:
 * - Step-through animation of acknowledgment levels
 * - Visual fading of messages to show uncertainty
 * - "Last message" vulnerability highlighting
 * - Contrast with TGP's bilateral construction
 */

import * as d3 from 'd3';
import { Colors, Timing } from './types.js';
import { createAnimationControls } from './animation-controls.js';

/**
 * Represents one level in the acknowledgment chain.
 */
class AckLevel {
    constructor(level, sender, label) {
        this.level = level;
        this.sender = sender; // 'alice' or 'bob'
        this.label = label;
        this.delivered = false;
        this.isLastMessage = false;
    }
}

export class InfiniteRegressVisualizer {
    /**
     * Create a new infinite regress visualizer.
     * @param {string|HTMLElement} container - Container selector or element
     */
    constructor(container) {
        this.container = typeof container === 'string'
            ? d3.select(container)
            : d3.select(container);

        this.width = 800;
        this.height = 450;
        this.margin = { top: 60, right: 40, bottom: 60, left: 40 };

        // Visualization state
        this.levels = [];
        this.currentLevel = 0;
        this.isAnimating = false;
        this.animationId = null;

        // Animation speed control
        this.speed = 1.0;
        this.isPaused = false;
        this.controls = null;

        // Colors
        this.colors = {
            alice: Colors.alice,
            bob: Colors.bob,
            arrow: Colors.muted,
            lost: Colors.error,
            text: Colors.text,
            bg: Colors.bgDark
        };

        // Create SVG
        this.svg = null;
        this.arrowGroup = null;
        this.labelGroup = null;
        this.questionGroup = null;

        this.init();
    }

    /**
     * Initialize the visualization.
     */
    init() {
        this.container.selectAll('*').remove();

        // Create animation controls
        const containerEl = this.container.node();
        this.controls = createAnimationControls({
            container: containerEl,
            defaultSpeed: 1.0,
            minSpeed: 0.25,
            maxSpeed: 2.0,
            step: 0.25,
            showStepControls: true,
            onSpeedChange: (speed) => {
                this.speed = speed;
            },
            onPlayPause: (isPlaying) => {
                this.isPaused = !isPlaying;
                if (isPlaying && !this.isAnimating) {
                    this.runDemo();
                }
            },
            onReset: () => {
                this.reset();
            },
            onStep: (direction) => {
                if (direction > 0) {
                    this.step();
                } else {
                    // Step backward: go back one level
                    if (this.currentLevel > 0) {
                        this.currentLevel--;
                        this.reset();
                        // Re-draw up to current level
                        for (let i = 0; i < this.currentLevel; i++) {
                            this.step();
                        }
                    }
                }
            }
        });

        this.svg = this.container.append('svg')
            .attr('viewBox', `0 0 ${this.width} ${this.height}`)
            .attr('class', 'regress-svg')
            .attr('role', 'graphics-document')
            .attr('aria-label', 'Infinite acknowledgment regress visualization');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', this.colors.bg);

        // Title
        this.svg.append('text')
            .attr('x', this.width / 2)
            .attr('y', 30)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '18px')
            .attr('font-weight', 'bold')
            .text('The Infinite Acknowledgment Problem');

        // Define arrow marker
        const defs = this.svg.append('defs');

        defs.append('marker')
            .attr('id', 'regress-arrow')
            .attr('viewBox', '0 0 10 10')
            .attr('refX', 8)
            .attr('refY', 5)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M 0 0 L 10 5 L 0 10 Z')
            .attr('fill', this.colors.arrow);

        defs.append('marker')
            .attr('id', 'regress-arrow-alice')
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
            .attr('id', 'regress-arrow-bob')
            .attr('viewBox', '0 0 10 10')
            .attr('refX', 8)
            .attr('refY', 5)
            .attr('markerWidth', 6)
            .attr('markerHeight', 6)
            .attr('orient', 'auto')
            .append('path')
            .attr('d', 'M 0 0 L 10 5 L 0 10 Z')
            .attr('fill', this.colors.bob);

        // Lost message marker (X)
        defs.append('marker')
            .attr('id', 'regress-lost')
            .attr('viewBox', '0 0 10 10')
            .attr('refX', 5)
            .attr('refY', 5)
            .attr('markerWidth', 8)
            .attr('markerHeight', 8)
            .attr('orient', 'auto')
            .append('text')
            .attr('x', 5)
            .attr('y', 8)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.lost)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('✗');

        // Party labels (fixed positions)
        this.svg.append('text')
            .attr('x', this.margin.left + 20)
            .attr('y', this.margin.top + 20)
            .attr('fill', this.colors.alice)
            .attr('font-size', '16px')
            .attr('font-weight', 'bold')
            .text('Alice');

        this.svg.append('text')
            .attr('x', this.width - this.margin.right - 20)
            .attr('y', this.margin.top + 20)
            .attr('text-anchor', 'end')
            .attr('fill', this.colors.bob)
            .attr('font-size', '16px')
            .attr('font-weight', 'bold')
            .text('Bob');

        // Vertical timeline lines
        const timelineY1 = this.margin.top + 40;
        const timelineY2 = this.height - this.margin.bottom;

        this.svg.append('line')
            .attr('x1', this.margin.left + 40)
            .attr('y1', timelineY1)
            .attr('x2', this.margin.left + 40)
            .attr('y2', timelineY2)
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '4,4')
            .attr('opacity', 0.5);

        this.svg.append('line')
            .attr('x1', this.width - this.margin.right - 40)
            .attr('y1', timelineY1)
            .attr('x2', this.width - this.margin.right - 40)
            .attr('y2', timelineY2)
            .attr('stroke', this.colors.bob)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '4,4')
            .attr('opacity', 0.5);

        // Create layer groups
        this.arrowGroup = this.svg.append('g').attr('class', 'arrows');
        this.labelGroup = this.svg.append('g').attr('class', 'labels');
        this.questionGroup = this.svg.append('g').attr('class', 'questions');

        // Initialize acknowledgment levels
        this.initLevels();
    }

    /**
     * Initialize the acknowledgment levels.
     */
    initLevels() {
        this.levels = [
            new AckLevel(0, 'alice', 'MSG: "Attack at dawn?"'),
            new AckLevel(1, 'bob', 'ACK: "I received your message"'),
            new AckLevel(2, 'alice', 'ACK²: "I know you received it"'),
            new AckLevel(3, 'bob', 'ACK³: "I know you know..."'),
            new AckLevel(4, 'alice', 'ACK⁴: "I know you know I know..."'),
            new AckLevel(5, 'bob', 'ACK⁵: "I know you know I know you know..."'),
            new AckLevel(6, 'alice', '...'),
            new AckLevel(7, 'bob', '∞')
        ];
        this.currentLevel = 0;
    }

    /**
     * Draw a single acknowledgment arrow.
     * @param {AckLevel} level - The acknowledgment level
     * @param {boolean} animate - Whether to animate the drawing
     */
    drawArrow(level, animate = true) {
        const innerWidth = this.width - this.margin.left - this.margin.right - 80;
        const aliceX = this.margin.left + 40;
        const bobX = this.width - this.margin.right - 40;
        const startY = this.margin.top + 60 + level.level * 45;

        const fromX = level.sender === 'alice' ? aliceX : bobX;
        const toX = level.sender === 'alice' ? bobX : aliceX;
        const color = level.sender === 'alice' ? this.colors.alice : this.colors.bob;
        const markerEnd = level.sender === 'alice' ? 'url(#regress-arrow-alice)' : 'url(#regress-arrow-bob)';

        // Draw arrow
        const arrow = this.arrowGroup.append('line')
            .attr('x1', fromX)
            .attr('y1', startY)
            .attr('x2', animate ? fromX : toX)
            .attr('y2', startY)
            .attr('stroke', color)
            .attr('stroke-width', 2)
            .attr('marker-end', markerEnd)
            .attr('opacity', level.isLastMessage ? 0.4 : 1);

        if (animate) {
            arrow.transition()
                .duration(Timing.proof)
                .attr('x2', toX);
        }

        // Draw label
        const labelX = (fromX + toX) / 2;
        const labelOffset = level.sender === 'alice' ? -12 : 12;

        const label = this.labelGroup.append('text')
            .attr('x', labelX)
            .attr('y', startY + labelOffset)
            .attr('text-anchor', 'middle')
            .attr('fill', color)
            .attr('font-size', level.level > 5 ? '14px' : '12px')
            .attr('font-family', 'monospace')
            .attr('opacity', animate ? 0 : (level.isLastMessage ? 0.4 : 1))
            .text(level.label);

        if (animate) {
            label.transition()
                .delay(Timing.proof / 2)
                .duration(Timing.normal)
                .attr('opacity', level.isLastMessage ? 0.4 : 1);
        }

        // Add question mark for last message
        if (level.isLastMessage) {
            const qX = level.sender === 'alice' ? toX + 15 : toX - 15;

            this.questionGroup.append('text')
                .attr('x', qX)
                .attr('y', startY + 5)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.lost)
                .attr('font-size', '20px')
                .attr('font-weight', 'bold')
                .attr('opacity', 0)
                .text('?')
                .transition()
                .delay(animate ? Timing.proof : 0)
                .duration(Timing.normal)
                .attr('opacity', 1);

            // Add "This could be the last message!" annotation
            const annotationY = startY + (level.sender === 'alice' ? -25 : 25);

            this.questionGroup.append('text')
                .attr('x', labelX)
                .attr('y', annotationY)
                .attr('text-anchor', 'middle')
                .attr('fill', this.colors.lost)
                .attr('font-size', '11px')
                .attr('font-style', 'italic')
                .attr('opacity', 0)
                .text('← Could be lost! One party left uncertain')
                .transition()
                .delay(animate ? Timing.proof + Timing.normal : 0)
                .duration(Timing.normal)
                .attr('opacity', 1);
        }
    }

    /**
     * Step forward one acknowledgment level.
     * @returns {boolean} True if there are more levels
     */
    step() {
        if (this.currentLevel >= this.levels.length) {
            return false;
        }

        // Mark current level as potentially the last message
        if (this.currentLevel > 0) {
            // Clear previous "last message" status
            this.levels[this.currentLevel - 1].isLastMessage = false;
        }
        this.levels[this.currentLevel].isLastMessage = true;

        // Redraw all arrows to reflect new state
        this.arrowGroup.selectAll('*').remove();
        this.labelGroup.selectAll('*').remove();
        this.questionGroup.selectAll('*').remove();

        for (let i = 0; i <= this.currentLevel; i++) {
            this.drawArrow(this.levels[i], i === this.currentLevel);
        }

        this.currentLevel++;
        return this.currentLevel < this.levels.length;
    }

    /**
     * Run the full demonstration automatically.
     * @param {number} interval - Time between steps in ms
     */
    runDemo(interval = 1200) {
        if (this.isAnimating) return;

        this.isAnimating = true;
        this.reset();

        const animate = () => {
            if (!this.isAnimating) return;

            // Respect pause state
            if (this.isPaused) {
                this.animationId = setTimeout(animate, 100);
                return;
            }

            const hasMore = this.step();

            if (hasMore && this.isAnimating) {
                // Apply speed multiplier (inverse: higher speed = shorter interval)
                const adjustedInterval = interval / this.speed;
                this.animationId = setTimeout(animate, adjustedInterval);
            } else {
                this.isAnimating = false;
                this.showConclusion();
            }
        };

        animate();
    }

    /**
     * Stop the running demonstration.
     */
    stop() {
        this.isAnimating = false;
        if (this.animationId) {
            clearTimeout(this.animationId);
            this.animationId = null;
        }
    }

    /**
     * Reset to initial state.
     */
    reset() {
        this.stop();
        this.currentLevel = 0;
        this.initLevels();
        this.arrowGroup.selectAll('*').remove();
        this.labelGroup.selectAll('*').remove();
        this.questionGroup.selectAll('*').remove();
    }

    /**
     * Show the conclusion after the demo completes.
     */
    showConclusion() {
        const conclusionY = this.height - 30;

        // Add conclusion text
        const conclusion = this.svg.append('g')
            .attr('class', 'conclusion')
            .attr('opacity', 0);

        conclusion.append('rect')
            .attr('x', this.width / 2 - 250)
            .attr('y', conclusionY - 20)
            .attr('width', 500)
            .attr('height', 35)
            .attr('rx', 6)
            .attr('fill', 'rgba(248, 81, 73, 0.15)')
            .attr('stroke', this.colors.lost)
            .attr('stroke-width', 1);

        conclusion.append('text')
            .attr('x', this.width / 2)
            .attr('y', conclusionY)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.lost)
            .attr('font-size', '14px')
            .attr('font-weight', 'bold')
            .text('Every message could be "the last" — coordination is impossible!');

        conclusion.transition()
            .duration(Timing.slow)
            .attr('opacity', 1);
    }

    /**
     * Clean up resources.
     */
    destroy() {
        this.stop();
        this.container.selectAll('*').remove();
    }
}

/**
 * Factory function to create the visualizer with controls.
 * @param {string} containerId - Container element ID
 * @returns {object} Visualizer instance and control methods
 */
export function createInfiniteRegressDemo(containerId) {
    const container = document.getElementById(containerId);
    if (!container) {
        console.error(`Container not found: ${containerId}`);
        return null;
    }

    const visualizer = new InfiniteRegressVisualizer(container);

    return {
        visualizer,
        step: () => visualizer.step(),
        runDemo: (interval) => visualizer.runDemo(interval),
        stop: () => visualizer.stop(),
        reset: () => visualizer.reset(),
        destroy: () => visualizer.destroy()
    };
}
