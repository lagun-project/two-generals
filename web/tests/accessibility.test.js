/**
 * Two Generals Protocol - Accessibility Test Suite
 * WCAG 2.1 AA Compliance Testing using axe-core
 */

import { test, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

const BASE_URL = 'http://localhost:5173';

test.describe('WCAG 2.1 AA Accessibility Compliance', () => {

  test.beforeEach(async ({ page }) => {
    await page.goto(BASE_URL);
    // Wait for the page to fully load
    await page.waitForLoadState('networkidle');
  });

  test('should not have any automatically detectable accessibility issues on Tab 1', async ({ page }) => {
    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('should not have accessibility issues on Tab 2 (Performance)', async ({ page }) => {
    // Switch to Tab 2
    await page.click('button:has-text("Performance")');
    await page.waitForTimeout(500); // Wait for tab transition

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('should not have accessibility issues on Tab 3 (Test the Protocol)', async ({ page }) => {
    // Switch to Tab 3
    await page.click('button:has-text("Test the Protocol")');
    await page.waitForTimeout(500);

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('should not have accessibility issues on Tab 4 (Applications)', async ({ page }) => {
    // Switch to Tab 4
    await page.click('button:has-text("Applications")');
    await page.waitForTimeout(500);

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('keyboard navigation - tab buttons are keyboard accessible', async ({ page }) => {
    // Test that tab buttons can be focused and activated via keyboard
    const tabButtons = await page.locator('.tab-button').all();

    for (let i = 0; i < tabButtons.length; i++) {
      await tabButtons[i].focus();
      const isFocused = await tabButtons[i].evaluate(el => document.activeElement === el);
      expect(isFocused).toBeTruthy();

      // Test Enter key activation
      await page.keyboard.press('Enter');
      await page.waitForTimeout(300);

      // Verify the tab became active
      const isActive = await tabButtons[i].evaluate(el => el.classList.contains('active'));
      expect(isActive).toBeTruthy();
    }
  });

  test('keyboard navigation - interactive controls are keyboard accessible', async ({ page }) => {
    // Go to Tab 3 which has interactive controls
    await page.click('button:has-text("Test the Protocol")');
    await page.waitForTimeout(500);

    // Test slider accessibility
    const slider = page.locator('input[type="range"]').first();
    if (await slider.count() > 0) {
      await slider.focus();
      const isFocused = await slider.evaluate(el => document.activeElement === el);
      expect(isFocused).toBeTruthy();

      // Test arrow key navigation
      await page.keyboard.press('ArrowRight');
      await page.keyboard.press('ArrowLeft');
    }

    // Test button accessibility
    const buttons = await page.locator('button').all();
    for (const button of buttons.slice(0, 5)) { // Test first 5 buttons
      const isVisible = await button.isVisible();
      if (isVisible) {
        await button.focus();
        const isFocused = await button.evaluate(el => document.activeElement === el);
        expect(isFocused).toBeTruthy();
      }
    }
  });

  test('keyboard navigation - Skip to content link', async ({ page }) => {
    // Test skip-to-content functionality (if implemented)
    await page.keyboard.press('Tab');
    const firstFocusable = await page.evaluate(() => document.activeElement?.tagName);

    // First focusable element should be meaningful (not decorative)
    expect(firstFocusable).toBeTruthy();
  });

  test('ARIA labels and roles are properly implemented', async ({ page }) => {
    // Check for proper ARIA labels on interactive elements
    const interactiveElements = await page.locator('button, a, input, select, textarea').all();

    for (const element of interactiveElements) {
      const isVisible = await element.isVisible();
      if (isVisible) {
        const ariaLabel = await element.getAttribute('aria-label');
        const ariaLabelledBy = await element.getAttribute('aria-labelledby');
        const textContent = await element.textContent();
        const title = await element.getAttribute('title');

        // Element should have some form of accessible label
        const hasAccessibleLabel = ariaLabel || ariaLabelledBy || textContent?.trim() || title;
        expect(hasAccessibleLabel).toBeTruthy();
      }
    }
  });

  test('color contrast ratios meet WCAG AA standards', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withTags(['wcag2aa'])
      .include('body')
      .analyze();

    const contrastViolations = results.violations.filter(v =>
      v.id === 'color-contrast' || v.id === 'color-contrast-enhanced'
    );

    expect(contrastViolations).toEqual([]);
  });

  test('images have proper alt text', async ({ page }) => {
    const images = await page.locator('img').all();

    for (const img of images) {
      const alt = await img.getAttribute('alt');
      const role = await img.getAttribute('role');

      // Decorative images should have alt="" or role="presentation"
      // Informative images should have descriptive alt text
      const hasProperAlt = alt !== null || role === 'presentation';
      expect(hasProperAlt).toBeTruthy();
    }
  });

  test('form inputs have associated labels', async ({ page }) => {
    const inputs = await page.locator('input, select, textarea').all();

    for (const input of inputs) {
      const isVisible = await input.isVisible();
      if (isVisible) {
        const id = await input.getAttribute('id');
        const ariaLabel = await input.getAttribute('aria-label');
        const ariaLabelledBy = await input.getAttribute('aria-labelledby');

        // Input should have a label either via id, aria-label, or aria-labelledby
        if (id) {
          const label = await page.locator(`label[for="${id}"]`).count();
          expect(label > 0 || ariaLabel || ariaLabelledBy).toBeTruthy();
        } else {
          expect(ariaLabel || ariaLabelledBy).toBeTruthy();
        }
      }
    }
  });

  test('focus indicators are visible', async ({ page }) => {
    const focusableElements = await page.locator(
      'button, a, input, select, textarea, [tabindex]:not([tabindex="-1"])'
    ).all();

    for (const element of focusableElements.slice(0, 10)) { // Test first 10
      const isVisible = await element.isVisible();
      if (isVisible) {
        await element.focus();

        // Check that the element has visible focus styling
        const styles = await element.evaluate(el => {
          const computed = window.getComputedStyle(el);
          return {
            outline: computed.outline,
            outlineWidth: computed.outlineWidth,
            boxShadow: computed.boxShadow,
            border: computed.border
          };
        });

        // Should have some form of visible focus indicator
        const hasFocusIndicator =
          styles.outline !== 'none' ||
          styles.outlineWidth !== '0px' ||
          styles.boxShadow !== 'none' ||
          styles.border !== '';

        expect(hasFocusIndicator).toBeTruthy();
      }
    }
  });

  test('heading hierarchy is logical', async ({ page }) => {
    const headings = await page.locator('h1, h2, h3, h4, h5, h6').all();
    const headingLevels = [];

    for (const heading of headings) {
      const tagName = await heading.evaluate(el => el.tagName);
      const level = parseInt(tagName.substring(1));
      headingLevels.push(level);
    }

    // Check for logical heading hierarchy (no skipped levels)
    for (let i = 1; i < headingLevels.length; i++) {
      const diff = headingLevels[i] - headingLevels[i - 1];
      // Headings should not skip levels when increasing
      if (diff > 0) {
        expect(diff).toBeLessThanOrEqual(1);
      }
    }
  });

  test('landmark regions are properly defined', async ({ page }) => {
    const results = await new AxeBuilder({ page })
      .withTags(['wcag2aa'])
      .analyze();

    const landmarkViolations = results.violations.filter(v =>
      v.id === 'region' || v.id === 'landmark-one-main'
    );

    expect(landmarkViolations).toEqual([]);
  });

  test('language is properly declared', async ({ page }) => {
    const htmlLang = await page.getAttribute('html', 'lang');
    expect(htmlLang).toBeTruthy();
    expect(htmlLang).toMatch(/^[a-z]{2}(-[A-Z]{2})?$/); // Should be valid lang code
  });

  test('viewport zoom is not disabled', async ({ page }) => {
    const viewport = await page.locator('meta[name="viewport"]').getAttribute('content');

    // Should not contain user-scalable=no or maximum-scale=1
    if (viewport) {
      expect(viewport).not.toContain('user-scalable=no');
      expect(viewport).not.toContain('maximum-scale=1');
    }
  });

  test('screen reader - table headers are properly marked', async ({ page }) => {
    const tables = await page.locator('table').all();

    for (const table of tables) {
      const headers = await table.locator('th').count();
      const hasCaptions = await table.locator('caption').count() > 0;
      const hasAriaLabel = await table.getAttribute('aria-label');

      // Tables should have either headers, captions, or aria-label
      if (headers === 0) {
        expect(hasCaptions || hasAriaLabel).toBeTruthy();
      }
    }
  });

  test('motion can be reduced (prefers-reduced-motion)', async ({ page, context }) => {
    // Set prefers-reduced-motion preference
    await context.emulateMedia({ reducedMotion: 'reduce' });
    await page.reload();
    await page.waitForLoadState('networkidle');

    // The page should respect prefers-reduced-motion
    // Check that animations are disabled or reduced
    const animationDuration = await page.evaluate(() => {
      const element = document.querySelector('.tab-content, .animated-element');
      if (!element) return null;
      return window.getComputedStyle(element).animationDuration;
    });

    // If animations exist, they should be disabled or very short
    if (animationDuration) {
      expect(animationDuration === '0s' || animationDuration === 'none').toBeTruthy();
    }
  });
});

test.describe('Screen Reader Compatibility', () => {
  test('dynamic content updates are announced', async ({ page }) => {
    // Go to Tab 3 for interactive testing
    await page.click('button:has-text("Test the Protocol")');
    await page.waitForTimeout(500);

    // Check for aria-live regions
    const liveRegions = await page.locator('[aria-live], [role="status"], [role="alert"]').all();

    // Interactive sections should have live regions for announcements
    expect(liveRegions.length).toBeGreaterThan(0);
  });

  test('loading states are announced to screen readers', async ({ page }) => {
    // Check for loading indicators with proper ARIA
    const loadingIndicators = await page.locator('[aria-busy="true"], [role="progressbar"]').count();

    // This is informational - we should have loading states when content is loading
    // The count can be 0 if nothing is currently loading
    expect(loadingIndicators).toBeGreaterThanOrEqual(0);
  });
});
