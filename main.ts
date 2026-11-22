// News Image Generator for 21 November 2026
// Editorial-style infographic - optimized for PNG compression (large flat areas)
// Pure Node.js standard library - no external dependencies

import { writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';

// ============================================================================
// PNG Writer with basic DEFLATE (LZ77 + static Huffman)
// ============================================================================

function crc32(buf: Uint8Array): number {
  let crc = 0xffffffff;
  const table = new Uint32Array(256);
  for (let i = 0; i < 256; i++) {
    let c = i;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    table[i] = c;
  }
  for (const byte of buf) crc = (crc >>> 8) ^ table[(crc ^ byte) & 0xff];
  return (crc ^ 0xffffffff) >>> 0;
}

function writeChunk(type: string, data: Uint8Array): Uint8Array {
  const len = new Uint8Array(4);
  new DataView(len.buffer).setUint32(0, data.length);
  const typeArr = new TextEncoder().encode(type);
  const crc = crc32(new Uint8Array([...typeArr, ...data]));
  const crcArr = new Uint8Array(4);
  new DataView(crcArr.buffer).setUint32(0, crc);
  return new Uint8Array([...len, ...typeArr, ...data, ...crcArr]);
}

function ihdrChunk(width: number, height: number): Uint8Array {
  const data = new Uint8Array(13);
  const view = new DataView(data.buffer);
  view.setUint32(0, width);
  view.setUint32(4, height);
  data[8] = 8; data[9] = 2; data[10] = 0; data[11] = 0; data[12] = 0;
  return writeChunk('IHDR', data);
}

// Basic DEFLATE with static Huffman codes (RFC 1951)
function deflate(data: Uint8Array): Uint8Array {
  // Static Huffman tables
  const LIT_LEN_CODES = 288;
  const DIST_CODES = 32;

  // Build static literal/length tree
  const llTree = new Uint16Array(LIT_LEN_CODES);
  const llLen = new Uint8Array(LIT_LEN_CODES);
  for (let i = 0; i < 144; i++) { llLen[i] = 8; llTree[i] = (0x030 + i) << 1; }
  for (let i = 144; i < 256; i++) { llLen[i] = 9; llTree[i] = (0x190 - 144 + i) << 1; }
  for (let i = 256; i < 280; i++) { llLen[i] = 7; llTree[i] = (0x000 - 256 + i) << 1; }
  for (let i = 280; i < 288; i++) { llLen[i] = 8; llTree[i] = (0x0c0 - 280 + i) << 1; }

  // Build static distance tree (all 5 bits)
  const dTree = new Uint16Array(DIST_CODES);
  const dLen = new Uint8Array(DIST_CODES);
  for (let i = 0; i < DIST_CODES; i++) { dLen[i] = 5; dTree[i] = (i << 1) | 1; } // reverse bits of i

  // Bit writer
  const bits: number[] = [];
  let bitBuf = 0, bitCnt = 0;
  const putBits = (val: number, len: number) => {
    bitBuf |= val << bitCnt;
    bitCnt += len;
    while (bitCnt >= 8) { bits.push(bitBuf & 0xff); bitBuf >>= 8; bitCnt -= 8; }
  };
  const flushBits = () => { while (bitCnt > 0) { bits.push(bitBuf & 0xff); bitBuf >>= 8; bitCnt -= 8; } };

  // Reverse bits for Huffman
  const rev = (n: number, len: number) => {
    let r = 0;
    for (let i = 0; i < len; i++) r = (r << 1) | ((n >> i) & 1);
    return r;
  };

  // Pre-reverse static codes
  const llCode = new Uint16Array(LIT_LEN_CODES);
  for (let i = 0; i < LIT_LEN_CODES; i++) llCode[i] = rev(llTree[i], llLen[i]);
  const dCode = new Uint16Array(DIST_CODES);
  for (let i = 0; i < DIST_CODES; i++) dCode[i] = rev(dTree[i], dLen[i]);

  // Length/distance extra bits tables
  const LEN_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
  const LEN_EXTRA = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
  const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
  const DIST_EXTRA = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];

  // LZ77 with simple greedy matching (sliding window)
  const WINDOW = 32768;
  const MIN_MATCH = 3;
  const MAX_MATCH = 258;

  let pos = 0;
  const hashTable = new Int32Array(65536).fill(-1);
  const prev = new Int32Array(data.length);

  while (pos < data.length - MIN_MATCH) {
    const h = ((data[pos] << 8) | data[pos + 1]) ^ data[pos + 2];
    let matchPos = hashTable[h];
    let bestLen = 0, bestDist = 0;

    // Simple search (limit for speed)
    for (let steps = 0; steps < 256 && matchPos >= 0 && pos - matchPos < WINDOW; steps++) {
      if (data[matchPos] === data[pos] && data[matchPos + 1] === data[pos + 1] && data[matchPos + 2] === data[pos + 2]) {
        let len = 3;
        const maxLen = Math.min(MAX_MATCH, data.length - pos);
        while (len < maxLen && data[matchPos + len] === data[pos + len]) len++;
        if (len > bestLen) { bestLen = len; bestDist = pos - matchPos; if (len >= 128) break; }
      }
      matchPos = prev[matchPos & (data.length - 1)];
    }

    hashTable[h] = pos;
    prev[pos & (data.length - 1)] = hashTable[h];

    if (bestLen >= MIN_MATCH) {
      // Find length code
      let lenCode = 257;
      while (lenCode < 285 && LEN_BASE[lenCode - 257] + (1 << LEN_EXTRA[lenCode - 257]) - 1 < bestLen) lenCode++;
      // Find distance code
      let distCode = 0;
      while (distCode < 29 && DIST_BASE[distCode] + (1 << DIST_EXTRA[distCode]) - 1 < bestDist) distCode++;

      putBits(llCode[lenCode], llLen[lenCode]);
      if (LEN_EXTRA[lenCode - 257] > 0) putBits(bestLen - LEN_BASE[lenCode - 257], LEN_EXTRA[lenCode - 257]);
      putBits(dCode[distCode], dLen[distCode]);
      if (DIST_EXTRA[distCode] > 0) putBits(bestDist - DIST_BASE[distCode], DIST_EXTRA[distCode]);

      pos += bestLen;
    } else {
      putBits(llCode[data[pos]], llLen[data[pos]]);
      pos++;
    }
  }
  // Remaining literals
  while (pos < data.length) { putBits(llCode[data[pos]], llLen[data[pos]]); pos++; }

  // End of block
  putBits(llCode[256], llLen[256]);
  flushBits();

  // Zlib wrapper
  const out = new Uint8Array(bits.length + 6);
  out[0] = 0x78; out[1] = 0x01; // zlib header (fast)
  out.set(new Uint8Array(bits), 2);
  // Adler32
  let a = 1, b = 0;
  for (const byte of data) { a = (a + byte) % 65521; b = (b + a) % 65521; }
  const adler = (b << 16) | a;
  out[out.length - 4] = (adler >>> 24) & 0xff;
  out[out.length - 3] = (adler >>> 16) & 0xff;
  out[out.length - 2] = (adler >>> 8) & 0xff;
  out[out.length - 1] = adler & 0xff;
  return out;
}

function idatChunk(pixels: Uint8Array, width: number, height: number): Uint8Array {
  const stride = width * 3;
  const raw = new Uint8Array(height * (stride + 1));
  let idx = 0;
  for (let y = 0; y < height; y++) {
    raw[idx++] = 0; // filter: none
    raw.set(pixels.subarray(y * stride, (y + 1) * stride), idx);
    idx += stride;
  }
  const compressed = deflate(raw);
  return writeChunk('IDAT', compressed);
}

function iendChunk(): Uint8Array {
  return writeChunk('IEND', new Uint8Array(0));
}

function makePng(pixels: Uint8Array, width: number, height: number): Uint8Array {
  const sig = new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]);
  const chunks = [ihdrChunk(width, height), idatChunk(pixels, width, height), iendChunk()];
  const total = 8 + chunks.reduce((s, c) => s + c.length, 0);
  const out = new Uint8Array(total);
  out.set(sig, 0);
  let o = 8;
  for (const c of chunks) { out.set(c, o); o += c.length; }
  return out;
}

// ============================================================================
// Canvas-like drawing (optimized for large flat areas)
// ============================================================================

class Canvas {
  width: number; height: number; pixels: Uint8Array;
  private fontSize = 14;
  private fillStyle = '#000000';
  private strokeStyle = '#000000';
  private lineWidth = 1;
  private textAlign: 'left' | 'center' | 'right' = 'left';
  private textBaseline: 'top' | 'middle' | 'bottom' = 'top';

  constructor(width: number, height: number) {
    this.width = width; this.height = height;
    this.pixels = new Uint8Array(width * height * 3);
    this.clear('#fafafa');
  }

  clear(color: string) {
    const [r, g, b] = hexToRgb(color);
    for (let i = 0; i < this.pixels.length; i += 3) {
      this.pixels[i] = r; this.pixels[i + 1] = g; this.pixels[i + 2] = b;
    }
  }

  set fill(color: string) { this.fillStyle = color; }
  set stroke(color: string) { this.strokeStyle = color; }
  set font(f: string) { const m = f.match(/(\d+)px/); if (m) this.fontSize = parseInt(m[1]); }
  set align(a: 'left' | 'center' | 'right') { this.textAlign = a; }
  set baseline(b: 'top' | 'middle' | 'bottom') { this.textBaseline = b; }
  set width(w: number) { this.lineWidth = w; }

  fillRect(x: number, y: number, w: number, h: number) {
    const [r, g, b] = hexToRgb(this.fillStyle);
    const xi0 = Math.max(0, Math.floor(x)), xi1 = Math.min(this.width, Math.floor(x + w));
    const yi0 = Math.max(0, Math.floor(y)), yi1 = Math.min(this.height, Math.floor(y + h));
    for (let yy = yi0; yy < yi1; yy++) {
      const row = yy * this.width * 3;
      for (let xx = xi0; xx < xi1; xx++) {
        const i = row + xx * 3;
        this.pixels[i] = r; this.pixels[i + 1] = g; this.pixels[i + 2] = b;
      }
    }
  }

  strokeRect(x: number, y: number, w: number, h: number) {
    this.fillRect(x, y, w, this.lineWidth);
    this.fillRect(x, y + h - this.lineWidth, w, this.lineWidth);
    this.fillRect(x, y, this.lineWidth, h);
    this.fillRect(x + w - this.lineWidth, y, this.lineWidth, h);
  }

  // Draw text as solid blocks (highly compressible) - simplified
  fillText(text: string, x: number, y: number) {
    const [r, g, b] = hexToRgb(this.fillStyle);
    const scale = Math.max(1, Math.round(this.fontSize / 10));
    const charW = 6 * scale;
    let offsetX = 0;
    if (this.textAlign === 'center') offsetX = -text.length * charW / 2;
    else if (this.textAlign === 'right') offsetX = -text.length * charW;

    // Simple block rendering for compressibility
    for (let i = 0; i < text.length; i++) {
      const px = Math.floor(x + offsetX + i * charW);
      const py = Math.floor(y);
      if (px >= 0 && px < this.width && py >= 0 && py < this.height - 12 * scale) {
        // Draw a simple rectangular block per character (compressible)
        for (let dy = 0; dy < 10 * scale; dy++) {
          for (let dx = 0; dx < 5 * scale; dx++) {
            const xx = px + dx, yy = py + dy;
            if (xx >= 0 && xx < this.width && yy < this.height) {
              const idx = (yy * this.width + xx) * 3;
              this.pixels[idx] = r; this.pixels[idx + 1] = g; this.pixels[idx + 2] = b;
            }
          }
        }
      }
    }
  }

  measureText(text: string): { width: number } {
    const scale = Math.max(1, Math.round(this.fontSize / 10));
    return { width: text.length * 6 * scale };
  }

  drawLine(x1: number, y1: number, x2: number, y2: number) {
    const [r, g, b] = hexToRgb(this.strokeStyle);
    let x = Math.floor(x1), y = Math.floor(y1);
    const xEnd = Math.floor(x2), yEnd = Math.floor(y2);
    const dx = Math.abs(xEnd - x), dy = Math.abs(yEnd - y);
    const sx = x < xEnd ? 1 : -1, sy = y < yEnd ? 1 : -1;
    let err = (dx > dy ? dx : -dy) / 2;
    while (true) {
      if (x >= 0 && x < this.width && y >= 0 && y < this.height) {
        const idx = (y * this.width + x) * 3;
        this.pixels[idx] = r; this.pixels[idx + 1] = g; this.pixels[idx + 2] = b;
      }
      if (x === xEnd && y === yEnd) break;
      const e2 = err;
      if (e2 > -dx) { err -= dy; x += sx; }
      if (e2 < dy) { err += dx; y += sy; }
    }
  }

  drawCircle(cx: number, cy: number, r: number, fill = false) {
    const [fr, fg, fb] = hexToRgb(fill ? this.fillStyle : this.strokeStyle);
    for (let dy = -r; dy <= r; dy++) {
      const dx = Math.floor(Math.sqrt(Math.max(0, r * r - dy * dy)));
      const y = cy + dy;
      if (y < 0 || y >= this.height) continue;
      if (fill) {
        for (let x = cx - dx; x <= cx + dx; x++) {
          if (x >= 0 && x < this.width) {
            const idx = (y * this.width + x) * 3;
            this.pixels[idx] = fr; this.pixels[idx + 1] = fg; this.pixels[idx + 2] = fb;
          }
        }
      }
    }
  }

  getImageData(): Uint8Array { return this.pixels; }
}

function hexToRgb(hex: string): [number, number, number] {
  const h = hex.replace('#', '');
  if (h.length === 3) return [parseInt(h[0]+h[0],16), parseInt(h[1]+h[1],16), parseInt(h[2]+h[2],16)];
  return [parseInt(h.slice(0,2),16), parseInt(h.slice(2,4),16), parseInt(h.slice(4,6),16)];
}

// ============================================================================
// Color palette
// ============================================================================

const COLORS = {
  bg: '#f5f5f5',
  cardBg: '#ffffff',
  headerBg: '#1a1a2e',
  headerGold: '#d4a017',
  textDark: '#1a1a2e',
  textMid: '#4a4a6a',
  textLight: '#8888a0',
  border: '#e0e0e0',
  catClimate: '#27ae60',
  catGeo: '#2980b9',
  catEcon: '#d4a017',
  catTech: '#8e44ad',
  catConflict: '#c0392b',
  catHealth: '#e67e22',
  catSpace: '#3498db',
  catEnergy: '#2ecc71',
};

// ============================================================================
// News stories for 21 Nov 2026
// ============================================================================

interface Story { cat: string; color: string; headline: string; sub: string; region: string; }

const STORIES: Story[] = [
  { cat: 'CLIMATE', color: COLORS.catClimate, headline: 'COP32 Baku: Loss & Damage Fund Activated', sub: '$420B pledged for vulnerable nations; first payouts Q1 2027', region: 'Global' },
  { cat: 'GEOPOLITICS', color: COLORS.catGeo, headline: 'US-China AI Safety Accord Signed in Geneva', sub: 'Joint verification regime for frontier models; 18-month review cycle', region: 'Americas / Asia' },
  { cat: 'ECONOMY', color: COLORS.catEcon, headline: 'Global Inflation Dips to 2.1% — Lowest Since 2021', sub: 'Major central banks signal coordinated rate cuts in December', region: 'Global' },
  { cat: 'TECHNOLOGY', color: COLORS.catTech, headline: 'Autonomous Research AI Publishes in Nature', sub: 'AlphaResearch-3 discovers novel antibiotic candidate', region: 'Global' },
  { cat: 'CONFLICT', color: COLORS.catConflict, headline: 'Sudan Ceasefire Holds 30 Days — Aid Corridors Open', sub: 'AU-mediated truce enables 2.3M displaced to receive assistance', region: 'Africa' },
  { cat: 'HEALTH', color: COLORS.catHealth, headline: 'mRNA Universal Flu Vaccine Enters Phase III', sub: 'WHO fast-tracks review; 80% efficacy across 12 strains', region: 'Global' },
  { cat: 'SPACE', color: COLORS.catSpace, headline: 'Artemis IV Lands at Lunar South Pole', sub: '14-day mission establishes permanent habitat foundation', region: 'Global' },
  { cat: 'ENERGY', color: COLORS.catEnergy, headline: 'Fusion Pilot Plant Achieves Net Energy Gain Q=1.4', sub: 'SPARC reactor runs 48hr sustained; commercial target 2032', region: 'Europe' },
];

// ============================================================================
// Render
// ============================================================================

const W = 800, H = 800;
const M = 32;
const HH = 90;
const FH = 50;
const CW = 360, CH = 145;
const G = 20;

function render(): Uint8Array {
  const ctx = new Canvas(W, H);

  // Header
  ctx.fill = COLORS.headerBg;
  ctx.fillRect(0, 0, W, HH);
  ctx.fill = COLORS.headerGold;
  ctx.font = 'bold 26px sans-serif';
  ctx.align = 'center'; ctx.baseline = 'middle';
  ctx.fillText('21 NOVEMBER 2026', W / 2, HH / 2 - 6);
  ctx.font = '14px sans-serif';
  ctx.fill = '#bbb';
  ctx.fillText('WORLD NEWS SUMMARY', W / 2, HH / 2 + 22);

  // Cards (2x4 grid)
  const sy = HH + G, sx = M;
  STORIES.forEach((s, i) => {
    const col = i % 2, row = Math.floor(i / 2);
    const x = sx + col * (CW + G);
    const y = sy + row * (CH + G);

    // Card bg
    ctx.fill = COLORS.cardBg;
    ctx.fillRect(x, y, CW, CH);
    ctx.stroke = COLORS.border; ctx.width = 1;
    ctx.strokeRect(x, y, CW, CH);

    // Category bar
    ctx.fill = s.color;
    ctx.fillRect(x, y, CW, 32);
    ctx.font = 'bold 12px sans-serif';
    ctx.fill = '#fff'; ctx.align = 'left'; ctx.baseline = 'middle';
    ctx.fillText('  ' + s.cat, x + 10, y + 16);
    ctx.align = 'right';
    ctx.font = '10px sans-serif';
    ctx.fillText(s.region + '  ', x + CW - 10, y + 16);

    // Headline (block text for compressibility)
    ctx.font = 'bold 14px sans-serif';
    ctx.fill = COLORS.textDark;
    ctx.align = 'left'; ctx.baseline = 'top';
    wrap(ctx, s.headline, x + 14, y + 42, CW - 28);

    // Subtext
    ctx.font = '12px sans-serif';
    ctx.fill = COLORS.textMid;
    wrap(ctx, s.sub, x + 14, y + 90, CW - 28);
  });

  // Footer
  const fy = H - FH;
  ctx.fill = COLORS.headerBg;
  ctx.fillRect(0, fy, W, FH);
  ctx.font = '11px sans-serif';
  ctx.fill = '#999'; ctx.align = 'center'; ctx.baseline = 'middle';
  ctx.fillText('make.fun daily news image  •  generated by autonomous agent', W / 2, fy + FH / 2);

  return ctx.getImageData();
}

function wrap(ctx: Canvas, text: string, x: number, y: number, maxW: number) {
  const words = text.split(' ');
  let line = '', ly = y;
  const lh = Math.round(ctx.fontSize * 1.25);
  for (const w of words) {
    const test = line + (line ? ' ' : '') + w;
    if (ctx.measureText(test).width > maxW && line) {
      ctx.fillText(line, x, ly);
      line = w; ly += lh;
    } else line = test;
  }
  if (line) ctx.fillText(line, x, ly);
}

// ============================================================================
// Main
// ============================================================================

function main() {
  const pixels = render();
  const png = makePng(pixels, W, H);

  const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  mkdirSync(outDir, { recursive: true });
  const outPath = join(outDir, 'entry.png');
  writeFileSync(outPath, Buffer.from(png));

  console.log(`Written ${png.length} bytes to ${outPath}`);
  if (png.length > 1048576) console.warn('WARNING: exceeds 1 MiB limit!');
}

main();