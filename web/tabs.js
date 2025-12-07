/**
 * Tab Navigation System for Two Generals Protocol Explainer
 *
 * Three-tab structure:
 * - Tab 1: The Problem & Solution (educational explainer)
 * - Tab 2: Live Protocol Comparison (performance benchmarks)
 * - Tab 3: Interactive Visualizer (existing simulation)
 */

export class TabController {
    /**
     * Initialize the tab navigation controller.
     * @param {string} containerSelector - CSS selector for the tab container
     */
    constructor(containerSelector = '.tab-container') {
        this.container = document.querySelector(containerSelector);
        if (!this.container) {
            console.error('Tab container not found:', containerSelector);
            return;
        }

        this.tabs = this.container.querySelectorAll('.tab-button');
        this.panes = this.container.querySelectorAll('.tab-pane');
        this.activeTab = 0;

        this.init();
    }

    /**
     * Initialize tab event listeners and restore state.
     */
    init() {
        // Bind click events to tabs
        this.tabs.forEach((tab, index) => {
            tab.addEventListener('click', () => this.switchTo(index));

            // Keyboard navigation
            tab.addEventListener('keydown', (e) => {
                if (e.key === 'ArrowRight') {
                    e.preventDefault();
                    this.switchTo((index + 1) % this.tabs.length);
                } else if (e.key === 'ArrowLeft') {
                    e.preventDefault();
                    this.switchTo((index - 1 + this.tabs.length) % this.tabs.length);
                } else if (e.key === 'Home') {
                    e.preventDefault();
                    this.switchTo(0);
                } else if (e.key === 'End') {
                    e.preventDefault();
                    this.switchTo(this.tabs.length - 1);
                }
            });
        });

        // Restore tab state from URL hash or localStorage
        const hash = window.location.hash.slice(1);
        const savedTab = parseInt(localStorage.getItem('tgp-active-tab') || '0', 10);

        if (hash === 'problem') {
            this.switchTo(0, false);
        } else if (hash === 'comparison') {
            this.switchTo(1, false);
        } else if (hash === 'visualizer') {
            this.switchTo(2, false);
        } else if (savedTab >= 0 && savedTab < this.tabs.length) {
            this.switchTo(savedTab, false);
        } else {
            this.switchTo(0, false);
        }
    }

    /**
     * Switch to a specific tab by index.
     * @param {number} index - Tab index (0-based)
     * @param {boolean} saveState - Whether to save state to localStorage
     */
    switchTo(index, saveState = true) {
        if (index < 0 || index >= this.tabs.length) return;

        // Update active tab
        this.tabs.forEach((tab, i) => {
            const isActive = i === index;
            tab.classList.toggle('active', isActive);
            tab.setAttribute('aria-selected', isActive.toString());
            tab.tabIndex = isActive ? 0 : -1;
        });

        // Update active pane
        this.panes.forEach((pane, i) => {
            const isActive = i === index;
            pane.classList.toggle('active', isActive);
            pane.setAttribute('aria-hidden', (!isActive).toString());
        });

        // Focus the new tab
        this.tabs[index].focus();

        // Update URL hash without scrolling
        const hashes = ['problem', 'comparison', 'visualizer'];
        history.replaceState(null, '', `#${hashes[index]}`);

        // Save to localStorage
        if (saveState) {
            localStorage.setItem('tgp-active-tab', index.toString());
        }

        // Dispatch custom event for other components to react
        this.container.dispatchEvent(new CustomEvent('tabchange', {
            detail: { index, tabId: hashes[index] }
        }));

        this.activeTab = index;
    }

    /**
     * Get the currently active tab index.
     * @returns {number}
     */
    getActiveIndex() {
        return this.activeTab;
    }
}

// Initialize tabs when DOM is ready
export function initTabs() {
    return new TabController('.tab-container');
}
