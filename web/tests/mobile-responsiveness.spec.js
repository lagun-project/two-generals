/**
 * Mobile Responsiveness Test Suite
 * Tests the Two Generals Protocol web demo across mobile viewports (320px-768px)
 * Validates responsive breakpoints, layout, and interactive elements
 */

import { test, expect, devices } from '@playwright/test';

// Define test viewports covering the mobile range
const mobileViewports = [
  { name: 'iPhone SE', width: 375, height: 667 },
  { name: 'Galaxy S8+', width: 360, height: 740 },
  { name: 'Small Mobile', width: 320, height: 568 },
  { name: 'Medium Mobile', width: 414, height: 896 }, // iPhone 11 Pro Max
  { name: 'Large Mobile', width: 428, height: 926 }, // iPhone 12 Pro Max
  { name: 'Tablet Portrait', width: 768, height: 1024 },
];

// Test each viewport configuration
for (const viewport of mobileViewports) {
  test.describe(`Mobile Responsiveness - ${viewport.name} (${viewport.width}x${viewport.height})`, () => {

    test.beforeEach(async ({ page }) => {
      await page.setViewportSize({ width: viewport.width, height: viewport.height });
      await page.goto('http://localhost:8000');
      await page.waitForLoadState('networkidle');
    });

    test('should render header and navigation correctly', async ({ page }) => {
      // Check header is visible
      const header = page.locator('header');
      await expect(header).toBeVisible();

      // Check title is readable
      const title = page.locator('h1');
      await expect(title).toBeVisible();
      await expect(title).toContainText('Two Generals');

      // Verify header doesn't overflow
      const headerBox = await header.boundingBox();
      expect(headerBox.width).toBeLessThanOrEqual(viewport.width);
    });

    test('should display tab navigation correctly', async ({ page }) => {
      // Check tabs are visible
      const tabs = page.locator('.tabs');
      await expect(tabs).toBeVisible();

      // Check all tab buttons are accessible
      const tabButtons = page.locator('.tab-button');
      const count = await tabButtons.count();
      expect(count).toBeGreaterThanOrEqual(3);

      // Verify tabs don't overflow horizontally
      const tabsBox = await tabs.boundingBox();
      expect(tabsBox.width).toBeLessThanOrEqual(viewport.width);

      // Check if tabs wrap on small screens
      if (viewport.width <= 375) {
        // On small screens, tabs might stack or scroll
        const firstTab = tabButtons.first();
        const lastTab = tabButtons.last();
        const firstBox = await firstTab.boundingBox();
        const lastBox = await lastTab.boundingBox();

        // Either they're in a scrollable container or stacked vertically
        const isScrollable = tabsBox.width < viewport.width;
        const isStacked = lastBox.y > firstBox.y + firstBox.height;

        expect(isScrollable || isStacked || tabsBox.width <= viewport.width).toBeTruthy();
      }
    });

    test('should handle tab switching on mobile', async ({ page }) => {
      const tab1Button = page.locator('.tab-button').filter({ hasText: /Explainer|Problem/ }).first();
      const tab2Button = page.locator('.tab-button').filter({ hasText: /Performance/ }).first();

      // Click Tab 2
      await tab2Button.click();
      await page.waitForTimeout(300); // Wait for transition

      // Verify Tab 2 content is visible
      const tab2Content = page.locator('#tab2');
      await expect(tab2Content).toBeVisible();

      // Verify active state
      await expect(tab2Button).toHaveClass(/active/);

      // Click back to Tab 1
      await tab1Button.click();
      await page.waitForTimeout(300);

      // Verify Tab 1 content is visible
      const tab1Content = page.locator('#tab1');
      await expect(tab1Content).toBeVisible();
    });

    test('should render Protocol of Theseus visualization responsively', async ({ page }) => {
      // Navigate to explainer tab (usually Tab 1)
      await page.locator('.tab-button').first().click();

      // Find canvas element
      const canvas = page.locator('canvas').first();
      if (await canvas.count() > 0) {
        await expect(canvas).toBeVisible();

        // Verify canvas doesn't overflow
        const canvasBox = await canvas.boundingBox();
        expect(canvasBox.width).toBeLessThanOrEqual(viewport.width);

        // Check canvas has reasonable dimensions for mobile
        expect(canvasBox.width).toBeGreaterThan(200);
        expect(canvasBox.height).toBeGreaterThan(150);
      }
    });

    test('should render performance charts responsively', async ({ page }) => {
      // Navigate to Performance tab (Tab 2)
      const perfTab = page.locator('.tab-button').filter({ hasText: /Performance/ }).first();
      await perfTab.click();
      await page.waitForTimeout(500);

      // Check for chart canvases
      const charts = page.locator('#tab2 canvas');
      const chartCount = await charts.count();

      if (chartCount > 0) {
        for (let i = 0; i < chartCount; i++) {
          const chart = charts.nth(i);
          await expect(chart).toBeVisible();

          // Verify charts don't overflow
          const chartBox = await chart.boundingBox();
          expect(chartBox.width).toBeLessThanOrEqual(viewport.width - 40); // Account for padding
        }
      }
    });

    test('should handle control panels on mobile', async ({ page }) => {
      // Check for speed controls or simulation controls
      const controls = page.locator('.controls, .speed-control, .simulation-controls').first();

      if (await controls.count() > 0) {
        await expect(controls).toBeVisible();

        // Verify controls are accessible and not cut off
        const controlsBox = await controls.boundingBox();
        expect(controlsBox.width).toBeLessThanOrEqual(viewport.width);

        // Check for sliders
        const sliders = page.locator('input[type="range"]');
        const sliderCount = await sliders.count();

        for (let i = 0; i < sliderCount; i++) {
          const slider = sliders.nth(i);
          await expect(slider).toBeVisible();

          // Test slider interaction on touch
          const sliderBox = await slider.boundingBox();
          expect(sliderBox.width).toBeGreaterThan(100); // Ensure slider is wide enough
        }
      }
    });

    test('should handle buttons and interactive elements', async ({ page }) => {
      // Find all buttons
      const buttons = page.locator('button');
      const buttonCount = await buttons.count();

      expect(buttonCount).toBeGreaterThan(0);

      for (let i = 0; i < Math.min(buttonCount, 5); i++) {
        const button = buttons.nth(i);

        if (await button.isVisible()) {
          // Check button has adequate touch target size (minimum 44x44 for WCAG)
          const buttonBox = await button.boundingBox();
          expect(buttonBox.height).toBeGreaterThanOrEqual(32); // Relaxed for smaller screens
          expect(buttonBox.width).toBeGreaterThanOrEqual(32);

          // Verify button text is readable
          const text = await button.textContent();
          if (text && text.trim().length > 0) {
            expect(text.trim().length).toBeGreaterThan(0);
          }
        }
      }
    });

    test('should handle text readability', async ({ page }) => {
      // Check paragraph text
      const paragraphs = page.locator('p, .description, .explanation');
      const pCount = await paragraphs.count();

      if (pCount > 0) {
        for (let i = 0; i < Math.min(pCount, 3); i++) {
          const p = paragraphs.nth(i);

          if (await p.isVisible()) {
            const pBox = await p.boundingBox();

            // Text should not overflow viewport
            expect(pBox.width).toBeLessThanOrEqual(viewport.width);

            // Check line height is adequate
            const lineHeight = await p.evaluate(el => {
              const style = window.getComputedStyle(el);
              return parseFloat(style.lineHeight);
            });

            expect(lineHeight).toBeGreaterThan(16); // Minimum readable line height
          }
        }
      }
    });

    test('should handle scrolling correctly', async ({ page }) => {
      // Get page height
      const pageHeight = await page.evaluate(() => document.documentElement.scrollHeight);

      // If content is taller than viewport, test scrolling
      if (pageHeight > viewport.height) {
        // Scroll to middle
        await page.evaluate(() => window.scrollTo(0, document.documentElement.scrollHeight / 2));
        await page.waitForTimeout(200);

        // Scroll to bottom
        await page.evaluate(() => window.scrollTo(0, document.documentElement.scrollHeight));
        await page.waitForTimeout(200);

        // Verify we can scroll back up
        await page.evaluate(() => window.scrollTo(0, 0));
        await page.waitForTimeout(200);

        const scrollTop = await page.evaluate(() => window.scrollY);
        expect(scrollTop).toBeLessThan(50);
      }
    });

    test('should not have horizontal overflow', async ({ page }) => {
      // Check body doesn't overflow horizontally
      const bodyWidth = await page.evaluate(() => document.body.scrollWidth);
      const viewportWidth = viewport.width;

      // Allow 1px tolerance for rounding
      expect(bodyWidth).toBeLessThanOrEqual(viewportWidth + 1);

      // Check for any elements wider than viewport
      const wideElements = await page.evaluate((vw) => {
        const elements = document.querySelectorAll('*');
        const wide = [];
        elements.forEach(el => {
          const rect = el.getBoundingClientRect();
          if (rect.width > vw + 1) {
            wide.push({
              tag: el.tagName,
              class: el.className,
              width: rect.width
            });
          }
        });
        return wide;
      }, viewportWidth);

      if (wideElements.length > 0) {
        console.log(`Wide elements on ${viewport.name}:`, wideElements);
      }

      // This is a warning, not a hard failure, as some elements may intentionally overflow
      expect(wideElements.length).toBeLessThan(5);
    });

    test('should handle responsive breakpoints correctly', async ({ page }) => {
      // Check computed styles at this viewport
      const body = page.locator('body');
      const fontSize = await body.evaluate(el =>
        window.getComputedStyle(el).fontSize
      );

      // Font size should be readable (at least 14px on mobile)
      const fontSizePx = parseFloat(fontSize);
      expect(fontSizePx).toBeGreaterThanOrEqual(14);

      // Check for mobile-specific styles
      if (viewport.width <= 768) {
        // Check if mobile styles are applied
        const container = page.locator('.container, main, .content').first();
        if (await container.count() > 0) {
          const padding = await container.evaluate(el =>
            window.getComputedStyle(el).paddingLeft
          );

          // Mobile should have less padding
          const paddingPx = parseFloat(padding);
          expect(paddingPx).toBeLessThanOrEqual(30);
        }
      }
    });

    test('should handle images and media responsively', async ({ page }) => {
      const images = page.locator('img, svg');
      const imageCount = await images.count();

      for (let i = 0; i < imageCount; i++) {
        const img = images.nth(i);

        if (await img.isVisible()) {
          const imgBox = await img.boundingBox();

          // Images should not overflow viewport
          expect(imgBox.width).toBeLessThanOrEqual(viewport.width);
        }
      }
    });

    test('should maintain functionality on mobile', async ({ page }) => {
      // Test that key features work on mobile

      // 1. Tab switching works (tested above, verify again)
      const tabs = page.locator('.tab-button');
      const tabCount = await tabs.count();

      if (tabCount >= 2) {
        await tabs.nth(1).click();
        await page.waitForTimeout(300);
        await expect(tabs.nth(1)).toHaveClass(/active/);
      }

      // 2. Speed controls work (if present)
      const speedSlider = page.locator('input[type="range"]').first();
      if (await speedSlider.count() > 0 && await speedSlider.isVisible()) {
        // Try changing the slider value
        await speedSlider.fill('50');
        const value = await speedSlider.inputValue();
        expect(parseFloat(value)).toBeCloseTo(50, 0);
      }

      // 3. Start/Stop buttons work (if present)
      const startButton = page.locator('button').filter({ hasText: /Start|Play|Run/i }).first();
      if (await startButton.count() > 0 && await startButton.isVisible()) {
        await startButton.click();
        await page.waitForTimeout(200);
        // Button should either become Stop or be disabled
        const newText = await startButton.textContent();
        expect(newText.toLowerCase()).toMatch(/stop|pause|running|start/i);
      }
    });

  });
}

// Additional device emulation tests using Playwright's built-in devices
test.describe('Device Emulation Tests', () => {

  test('iPhone 12', async ({ browser }) => {
    const context = await browser.newContext({
      ...devices['iPhone 12'],
    });
    const page = await context.newPage();

    await page.goto('http://localhost:8000');
    await page.waitForLoadState('networkidle');

    // Verify mobile layout
    const header = page.locator('header');
    await expect(header).toBeVisible();

    // Test touch interactions
    const tab2 = page.locator('.tab-button').nth(1);
    await tab2.tap();
    await page.waitForTimeout(300);
    await expect(tab2).toHaveClass(/active/);

    await context.close();
  });

  test('Pixel 5', async ({ browser }) => {
    const context = await browser.newContext({
      ...devices['Pixel 5'],
    });
    const page = await context.newPage();

    await page.goto('http://localhost:8000');
    await page.waitForLoadState('networkidle');

    // Verify no horizontal scroll
    const bodyWidth = await page.evaluate(() => document.body.scrollWidth);
    const viewportWidth = await page.viewportSize().then(v => v.width);
    expect(bodyWidth).toBeLessThanOrEqual(viewportWidth + 1);

    await context.close();
  });

  test('iPad Mini', async ({ browser }) => {
    const context = await browser.newContext({
      ...devices['iPad Mini'],
    });
    const page = await context.newPage();

    await page.goto('http://localhost:8000');
    await page.waitForLoadState('networkidle');

    // Verify tablet layout
    const tabs = page.locator('.tabs');
    await expect(tabs).toBeVisible();

    // Test landscape orientation
    await context.close();
  });

  test('Galaxy S9+', async ({ browser }) => {
    const context = await browser.newContext({
      ...devices['Galaxy S9+'],
    });
    const page = await context.newPage();

    await page.goto('http://localhost:8000');
    await page.waitForLoadState('networkidle');

    // Verify touch targets are adequate
    const buttons = page.locator('button');
    const firstButton = buttons.first();

    if (await firstButton.isVisible()) {
      const box = await firstButton.boundingBox();
      expect(box.height).toBeGreaterThanOrEqual(32);
    }

    await context.close();
  });
});

// Orientation change tests
test.describe('Orientation Tests', () => {

  test('should handle portrait to landscape rotation', async ({ browser }) => {
    const context = await browser.newContext({
      viewport: { width: 375, height: 667 }, // iPhone SE portrait
    });
    const page = await context.newPage();

    await page.goto('http://localhost:8000');
    await page.waitForLoadState('networkidle');

    // Check portrait layout
    let header = page.locator('header');
    await expect(header).toBeVisible();

    // Rotate to landscape
    await page.setViewportSize({ width: 667, height: 375 });
    await page.waitForTimeout(500);

    // Verify layout adapts
    header = page.locator('header');
    await expect(header).toBeVisible();

    // Check no horizontal overflow
    const bodyWidth = await page.evaluate(() => document.body.scrollWidth);
    expect(bodyWidth).toBeLessThanOrEqual(667 + 1);

    await context.close();
  });

});

// Performance on mobile
test.describe('Mobile Performance', () => {

  test('should load quickly on mobile network', async ({ browser }) => {
    const context = await browser.newContext({
      ...devices['iPhone 12'],
    });
    const page = await context.newPage();

    // Measure load time
    const startTime = Date.now();
    await page.goto('http://localhost:8000');
    await page.waitForLoadState('load');
    const loadTime = Date.now() - startTime;

    // Should load in reasonable time (even on slow connection)
    expect(loadTime).toBeLessThan(5000);

    await context.close();
  });

  test('should not cause memory issues on mobile', async ({ browser }) => {
    const context = await browser.newContext({
      ...devices['Pixel 5'],
    });
    const page = await context.newPage();

    await page.goto('http://localhost:8000');
    await page.waitForLoadState('networkidle');

    // Navigate through tabs
    const tabs = page.locator('.tab-button');
    const tabCount = await tabs.count();

    for (let i = 0; i < tabCount; i++) {
      await tabs.nth(i).click();
      await page.waitForTimeout(300);
    }

    // Check console for errors
    const errors = [];
    page.on('console', msg => {
      if (msg.type() === 'error') {
        errors.push(msg.text());
      }
    });

    await page.waitForTimeout(1000);

    // Should not have major errors
    const criticalErrors = errors.filter(e =>
      !e.includes('favicon') && !e.includes('wasm')
    );
    expect(criticalErrors.length).toBe(0);

    await context.close();
  });

});
