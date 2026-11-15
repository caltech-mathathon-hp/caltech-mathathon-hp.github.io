import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

/** the step-through page: `npm run stepper` (dev server), `npm run stepper:build` (static files in out/stepper) */
export default defineConfig({
  root: 'stepper',
  base: './',
  plugins: [react()],
  server: { port: 5199, strictPort: true },
  build: { outDir: '../out/stepper', emptyOutDir: true, chunkSizeWarningLimit: 4000 },
});
