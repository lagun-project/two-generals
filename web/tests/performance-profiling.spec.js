/**
 * Performance Profiling Test Suite for TGP Web Demo
 *
 * Verifies:
 * - <2s initial load time
 * - 60fps animations
 * - <300ms tab switching
 *
 * Uses Playwright with Chrome DevTools Protocol for precise measurements
 */

import { test, expect } from '@playwright/test';

const BASE_URL = 'http://localhost:5173'; // Vite dev server
const PERFORMANCE_TARGETS = {
  initialLoad: 2000,        // <2s
  targetFPS: 60,            // 60fps
  minAcceptableFPS: 55,     // Allow 5fps drop
  tabSwitch: 300,           // <300ms
  firstPaint: 1000,         // <1s
  firstContentfulPaint: 1500, // <1.5s
};

test.describe('Performance Profiling', () => {

  test('Initial Load Time < 2s', async ({ page }) => {
    // Enable performance metrics
    const client = await page.context().newCDPSession(page);
    await client.send('Performance.enable');

    const startTime = Date.now();

    // Navigate and wait for load event
    await page.goto(BASE_URL, { waitUntil: 'load' });

    const loadTime = Date.now() - startTime;

    // Get detailed performance metrics
    const performanceMetrics = await client.send('Performance.getMetrics');

    // Get navigation timing from the page
    const timing = await page.evaluate(() => {
      const perf = performance.getEntriesByType('navigation')[0];
      return {
        domContentLoaded: perf.domContentLoadedEventEnd - perf.fetchStart,
        loadComplete: perf.loadEventEnd - perf.fetchStart,
        domInteractive: perf.domInteractive - perf.fetchStart,
        firstPaint: performance.getEntriesByType('paint').find(e => e.name === 'first-paint')?.startTime || 0,
        firstContentfulPaint: performance.getEntriesByType('paint').find(e => e.name === 'first-contentful-paint')?.startTime || 0,
      };
    });

    console.log('\n=== Initial Load Performance ===');
    console.log(`Total Load Time: ${loadTime}ms (target: <${PERFORMANCE_TARGETS.initialLoad}ms)`);
    console.log(`First Paint: ${timing.firstPaint.toFixed(0)}ms (target: <${PERFORMANCE_TARGETS.firstPaint}ms)`);
    console.log(`First Contentful Paint: ${timing.firstContentfulPaint.toFixed(0)}ms (target: <${PERFORMANCE_TARGETS.firstContentfulPaint}ms)`);
    console.log(`DOM Interactive: ${timing.domInteractive.toFixed(0)}ms`);
    console.log(`DOM Content Loaded: ${timing.domContentLoaded.toFixed(0)}ms`);
    console.log(`Load Complete: ${timing.loadComplete.toFixed(0)}ms`);

    // Assertions
    expect(loadTime, `Load time ${loadTime}ms should be < ${PERFORMANCE_TARGETS.initialLoad}ms`).toBeLessThan(PERFORMANCE_TARGETS.initialLoad);
    expect(timing.firstPaint, `First paint ${timing.firstPaint}ms should be < ${PERFORMANCE_TARGETS.firstPaint}ms`).toBeLessThan(PERFORMANCE_TARGETS.firstPaint);
    expect(timing.firstContentfulPaint, `FCP ${timing.firstContentfulPaint}ms should be < ${PERFORMANCE_TARGETS.firstContentfulPaint}ms`).toBeLessThan(PERFORMANCE_TARGETS.firstContentfulPaint);
  });

  test('Tab Switching Performance < 300ms', async ({ page }) => {
    await page.goto(BASE_URL, { waitUntil: 'load' });

    // Wait for initial render
    await page.waitForSelector('.tab-container');

    const tabSwitchTimings = [];

    // Test switching between all tabs
    const tabs = ['tab-problem', 'tab-comparison', 'tab-visualizer'];

    for (const tabId of tabs) {
      const startTime = performance.now();

      // Click the tab
      await page.click(`#${tabId}`);

      // Wait for tab pane to become active
      const paneId = tabId.replace('tab-', 'pane-');
      await page.waitForSelector(`#${paneId}.active`, { timeout: 5000 });

      const switchTime = performance.now() - startTime;
      tabSwitchTimings.push({ tab: tabId, time: switchTime });

      console.log(`Tab switch to ${tabId}: ${switchTime.toFixed(2)}ms`);

      // Allow a brief moment for any animations
      await page.waitForTimeout(100);
    }

    console.log('\n=== Tab Switching Performance ===');
    tabSwitchTimings.forEach(({ tab, time }) => {
      console.log(`${tab}: ${time.toFixed(2)}ms (target: <${PERFORMANCE_TARGETS.tabSwitch}ms)`);
    });

    // Average switch time
    const avgSwitchTime = tabSwitchTimings.reduce((sum, t) => sum + t.time, 0) / tabSwitchTimings.length;
    console.log(`Average: ${avgSwitchTime.toFixed(2)}ms`);

    // All switches should be under 300ms
    tabSwitchTimings.forEach(({ tab, time }) => {
      expect(time, `${tab} switch time ${time.toFixed(0)}ms should be < ${PERFORMANCE_TARGETS.tabSwitch}ms`).toBeLessThan(PERFORMANCE_TARGETS.tabSwitch);
    });

    expect(avgSwitchTime, `Average switch time ${avgSwitchTime.toFixed(0)}ms should be < ${PERFORMANCE_TARGETS.tabSwitch}ms`).toBeLessThan(PERFORMANCE_TARGETS.tabSwitch);
  });

  test('60fps Animation Performance', async ({ page }) => {
    await page.goto(BASE_URL, { waitUntil: 'load' });

    // Navigate to Tab 3 (Interactive Visualizer) which has continuous animations
    await page.click('#tab-visualizer');
    await page.waitForSelector('#pane-visualizer.active');

    // Start the protocol simulation
    const startButton = await page.waitForSelector('#start-btn');

    // Enable FPS tracking via CDP
    const client = await page.context().newCDPSession(page);

    // Start performance recording
    await client.send('Performance.enable');

    // Track frame rate
    const frameRates = [];
    const fpsSamples = [];

    let frameCount = 0;
    let lastFrameTime = Date.now();

    // Set up frame tracking
    const collectFPS = page.evaluateHandle(() => {
      return new Promise((resolve) => {
        const fpsData = [];
        let frameCount = 0;
        let lastTime = performance.now();
        let animationId;

        const measureFPS = (currentTime) => {
          frameCount++;
          const deltaTime = currentTime - lastTime;

          // Sample FPS every second
          if (deltaTime >= 1000) {
            const fps = (frameCount * 1000) / deltaTime;
            fpsData.push(fps);
            frameCount = 0;
            lastTime = currentTime;

            // Collect for 3 seconds
            if (fpsData.length >= 3) {
              cancelAnimationFrame(animationId);
              resolve(fpsData);
              return;
            }
          }

          animationId = requestAnimationFrame(measureFPS);
        };

        requestAnimationFrame(measureFPS);
      });
    });

    // Start the animation
    await startButton.click();

    // Wait for FPS collection to complete
    const fpsData = await collectFPS.then(handle => handle.jsonValue());

    console.log('\n=== Animation Performance (60fps target) ===');
    fpsData.forEach((fps, index) => {
      console.log(`Second ${index + 1}: ${fps.toFixed(2)} fps`);
    });

    const avgFPS = fpsData.reduce((sum, fps) => sum + fps, 0) / fpsData.length;
    const minFPS = Math.min(...fpsData);

    console.log(`Average FPS: ${avgFPS.toFixed(2)}`);
    console.log(`Minimum FPS: ${minFPS.toFixed(2)}`);
    console.log(`Target: ≥${PERFORMANCE_TARGETS.minAcceptableFPS} fps`);

    // Check that average FPS is acceptable
    expect(avgFPS, `Average FPS ${avgFPS.toFixed(1)} should be ≥ ${PERFORMANCE_TARGETS.minAcceptableFPS}`).toBeGreaterThanOrEqual(PERFORMANCE_TARGETS.minAcceptableFPS);

    // Check that no sample drops below threshold
    expect(minFPS, `Minimum FPS ${minFPS.toFixed(1)} should be ≥ ${PERFORMANCE_TARGETS.minAcceptableFPS}`).toBeGreaterThanOrEqual(PERFORMANCE_TARGETS.minAcceptableFPS);
  });

  test('Bundle Size and Resource Loading', async ({ page }) => {
    const client = await page.context().newCDPSession(page);
    await client.send('Network.enable');

    const resources = [];

    client.on('Network.responseReceived', (event) => {
      const response = event.response;
      if (response.url.includes(BASE_URL)) {
        resources.push({
          url: response.url,
          type: event.type,
          status: response.status,
          mimeType: response.mimeType,
        });
      }
    });

    client.on('Network.loadingFinished', async (event) => {
      const resource = resources.find(r => r.url.includes(event.requestId));
      if (resource) {
        try {
          const body = await client.send('Network.getResponseBody', {
            requestId: event.requestId
          });
          resource.size = body.body.length;
        } catch (e) {
          // Some resources don't have accessible bodies
        }
      }
    });

    await page.goto(BASE_URL, { waitUntil: 'networkidle' });

    // Wait a bit for all resources to be captured
    await page.waitForTimeout(1000);

    console.log('\n=== Resource Loading Analysis ===');

    let totalSize = 0;
    let jsSize = 0;
    let cssSize = 0;

    resources.forEach(resource => {
      const size = resource.size || 0;
      totalSize += size;

      if (resource.mimeType?.includes('javascript')) {
        jsSize += size;
      } else if (resource.mimeType?.includes('css')) {
        cssSize += size;
      }

      if (size > 10000) { // Only log resources > 10KB
        console.log(`${resource.type}: ${(size / 1024).toFixed(2)}KB - ${resource.url.split('/').pop()}`);
      }
    });

    console.log(`\nTotal JavaScript: ${(jsSize / 1024).toFixed(2)}KB`);
    console.log(`Total CSS: ${(cssSize / 1024).toFixed(2)}KB`);
    console.log(`Total Resources: ${(totalSize / 1024).toFixed(2)}KB`);

    // Bundle size target: <500KB
    expect(totalSize / 1024, 'Total bundle size should be reasonable (<500KB)').toBeLessThan(500);
  });

  test('Memory Usage During Animations', async ({ page }) => {
    const client = await page.context().newCDPSession(page);

    await page.goto(BASE_URL, { waitUntil: 'load' });

    // Navigate to visualizer tab
    await page.click('#tab-visualizer');
    await page.waitForSelector('#pane-visualizer.active');

    // Measure initial memory
    const initialMetrics = await client.send('Performance.getMetrics');
    const initialMemory = initialMetrics.metrics.find(m => m.name === 'JSHeapUsedSize')?.value || 0;

    // Start animation
    await page.click('#start-btn');

    // Let it run for 5 seconds
    await page.waitForTimeout(5000);

    // Measure memory after animations
    const afterMetrics = await client.send('Performance.getMetrics');
    const afterMemory = afterMetrics.metrics.find(m => m.name === 'JSHeapUsedSize')?.value || 0;

    const memoryIncrease = (afterMemory - initialMemory) / (1024 * 1024); // Convert to MB

    console.log('\n=== Memory Usage ===');
    console.log(`Initial Memory: ${(initialMemory / (1024 * 1024)).toFixed(2)}MB`);
    console.log(`After 5s Animation: ${(afterMemory / (1024 * 1024)).toFixed(2)}MB`);
    console.log(`Memory Increase: ${memoryIncrease.toFixed(2)}MB`);

    // Memory increase should be reasonable (<50MB for 5 seconds of animation)
    expect(memoryIncrease, 'Memory increase should be reasonable (<50MB)').toBeLessThan(50);
  });

  test('Performance Summary Report', async ({ page }) => {
    const client = await page.context().newCDPSession(page);
    await client.send('Performance.enable');

    const startTime = Date.now();
    await page.goto(BASE_URL, { waitUntil: 'load' });
    const loadTime = Date.now() - startTime;

    // Get comprehensive metrics
    const timing = await page.evaluate(() => {
      const perf = performance.getEntriesByType('navigation')[0];
      const paint = performance.getEntriesByType('paint');

      return {
        dns: perf.domainLookupEnd - perf.domainLookupStart,
        tcp: perf.connectEnd - perf.connectStart,
        ttfb: perf.responseStart - perf.requestStart,
        download: perf.responseEnd - perf.responseStart,
        domProcessing: perf.domComplete - perf.domLoading,
        firstPaint: paint.find(e => e.name === 'first-paint')?.startTime || 0,
        firstContentfulPaint: paint.find(e => e.name === 'first-contentful-paint')?.startTime || 0,
        domInteractive: perf.domInteractive - perf.fetchStart,
        domContentLoaded: perf.domContentLoadedEventEnd - perf.fetchStart,
        loadComplete: perf.loadEventEnd - perf.fetchStart,
      };
    });

    console.log('\n╔════════════════════════════════════════════════════════════╗');
    console.log('║         TGP WEB DEMO - PERFORMANCE SUMMARY REPORT          ║');
    console.log('╠════════════════════════════════════════════════════════════╣');
    console.log(`║ DNS Lookup:              ${timing.dns.toFixed(0).padStart(6)}ms                          ║`);
    console.log(`║ TCP Connection:          ${timing.tcp.toFixed(0).padStart(6)}ms                          ║`);
    console.log(`║ Time to First Byte:      ${timing.ttfb.toFixed(0).padStart(6)}ms                          ║`);
    console.log(`║ Download Time:           ${timing.download.toFixed(0).padStart(6)}ms                          ║`);
    console.log(`║ DOM Processing:          ${timing.domProcessing.toFixed(0).padStart(6)}ms                          ║`);
    console.log('╠════════════════════════════════════════════════════════════╣');
    console.log(`║ First Paint (FP):        ${timing.firstPaint.toFixed(0).padStart(6)}ms  ${timing.firstPaint < PERFORMANCE_TARGETS.firstPaint ? '✓' : '✗'} (<${PERFORMANCE_TARGETS.firstPaint}ms)     ║`);
    console.log(`║ First Contentful Paint:  ${timing.firstContentfulPaint.toFixed(0).padStart(6)}ms  ${timing.firstContentfulPaint < PERFORMANCE_TARGETS.firstContentfulPaint ? '✓' : '✗'} (<${PERFORMANCE_TARGETS.firstContentfulPaint}ms)     ║`);
    console.log(`║ DOM Interactive:         ${timing.domInteractive.toFixed(0).padStart(6)}ms                          ║`);
    console.log(`║ DOM Content Loaded:      ${timing.domContentLoaded.toFixed(0).padStart(6)}ms                          ║`);
    console.log(`║ Load Complete:           ${timing.loadComplete.toFixed(0).padStart(6)}ms  ${timing.loadComplete < PERFORMANCE_TARGETS.initialLoad ? '✓' : '✗'} (<${PERFORMANCE_TARGETS.initialLoad}ms)     ║`);
    console.log('╠════════════════════════════════════════════════════════════╣');
    console.log(`║ Target: Initial Load < 2s          ${loadTime < PERFORMANCE_TARGETS.initialLoad ? '✓ PASS' : '✗ FAIL'}              ║`);
    console.log(`║ Target: 60fps Animations           (See separate test)    ║`);
    console.log(`║ Target: Tab Switch < 300ms         (See separate test)    ║`);
    console.log('╚════════════════════════════════════════════════════════════╝\n');

    // Final assertion for load time
    expect(loadTime).toBeLessThan(PERFORMANCE_TARGETS.initialLoad);
  });
});
