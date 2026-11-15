import { Config } from '@remotion/cli/config';

// WebGL in headless Chrome on macOS: ANGLE draws the three.js scenes.
Config.setChromiumOpenGlRenderer('angle');
Config.setVideoImageFormat('jpeg');
Config.setJpegQuality(92);
Config.setCodec('h264');
Config.setCrf(18);
Config.setPixelFormat('yuv420p');
Config.setConcurrency(6);
