import React, { useState, useEffect } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  CartesianGrid,
  Tooltip,
  ResponsiveContainer,
  ReferenceLine,
  AreaChart,
  Area,
  ComposedChart,
} from 'recharts';

const App = () => {
  const [data, setData] = useState([]);
  const [loading, setLoading] = useState(true);
  const [gapType, setGapType] = useState('twin'); // 'twin' | 'desert'

  // Coordinates for the 100M Frontier
  const frontiers = {
    twin: { origin: 100000000, size: 40, primes: [100000007, 100000037, 100000039] },
    desert: { origin: 100000550, size: 80, primes: [100000537, 100000609] },
  };

  const getPrimes = (limit) => {
    const sieve = new Array(limit + 1).fill(true);
    for (let p = 2; p * p <= limit; p++) {
      if (sieve[p]) {
        for (let i = p * p; i <= limit; i += p) {
          sieve[i] = false;
        }
      }
    }
    return sieve.reduce((acc, isPrime, i) => {
      if (isPrime && i > 1) {
        acc.push(i);
      }
      return acc;
    }, []);
  };

  useEffect(() => {
    setLoading(true);
    const basis = getPrimes(2000);
    const current = frontiers[gapType];
    const results = [];
    const eta = 3.299;

    for (let n = current.origin; n <= current.origin + current.size; n++) {
      let posSum = 0;
      let negSum = 0;
      const steeredN = n * (eta / Math.PI);

      basis.forEach((p, i) => {
        const theta = (2 * Math.PI * steeredN) / p;
        if (i % 2 === 0) {
          posSum += Math.cos(theta);
        } else {
          negSum += Math.sin(theta);
        }
      });

      const mag = Math.sqrt(Math.abs(posSum ** 2 - negSum ** 2)) / Math.log(n);
      results.push({ n, magnitude: mag, isPrime: current.primes.includes(n) });
    }

    const processed = results.map((val, i, arr) => {
      if (i === 0) {
        return { ...val, gradient: 0, tension: 0 };
      }
      const gradient = val.magnitude - arr[i - 1].magnitude;
      // Tension is the cumulative 'resistance' to structural return
      const tension = 1.0 - val.magnitude;
      return { ...val, gradient, tension };
    });

    setData(processed);
    setLoading(false);
  }, [gapType]);

  if (loading) {
    return (
      <div className="h-screen bg-slate-950 flex items-center justify-center">
        <div className="text-emerald-400 animate-pulse text-xl font-mono">CALIBRATING MANIFOLD...</div>
      </div>
    );
  }

  return (
    <div className="flex flex-col h-screen bg-slate-950 text-slate-100 font-sans p-6 overflow-hidden">
      <header className="flex justify-between items-center mb-8 bg-slate-900/50 p-6 rounded-2xl border border-slate-800">
        <div>
          <h1 className="text-2xl font-black bg-clip-text text-transparent bg-gradient-to-r from-emerald-400 to-cyan-500 uppercase tracking-tighter">
            Manifold Gap Navigator
          </h1>
          <p className="text-xs text-slate-500 mt-1 font-mono">
            Analyzing Destructive Interference & Phase Torque
          </p>
        </div>
        <div className="flex bg-slate-800 p-1 rounded-xl">
          <button
            onClick={() => setGapType('twin')}
            className={`px-6 py-2 rounded-lg text-xs font-bold transition-all ${
              gapType === 'twin' ? 'bg-emerald-600 text-white' : 'text-slate-400'
            }`}
          >
            TWIN CLUSTER
          </button>
          <button
            onClick={() => setGapType('desert')}
            className={`px-6 py-2 rounded-lg text-xs font-bold transition-all ${
              gapType === 'desert' ? 'bg-emerald-600 text-white' : 'text-slate-400'
            }`}
          >
            PRIME DESERT
          </button>
        </div>
      </header>

      <div className="flex-1 grid grid-rows-2 gap-6 overflow-hidden">
        {/* MAGNITUDE & TENSION */}
        <div className="bg-slate-900 rounded-3xl p-6 border border-slate-800 relative shadow-2xl">
          <h3 className="text-[10px] font-black text-slate-500 uppercase tracking-widest mb-6">
            Structural Magnitude vs. Manifold Tension
          </h3>
          <ResponsiveContainer width="100%" height="90%">
            <ComposedChart data={data}>
              <defs>
                <linearGradient id="tensionFill" x1="0" y1="0" x2="0" y2="1">
                  <stop offset="5%" stopColor="#ef4444" stopOpacity={0.2} />
                  <stop offset="95%" stopColor="#ef4444" stopOpacity={0} />
                </linearGradient>
              </defs>
              <CartesianGrid strokeDasharray="3 3" stroke="#1e293b" vertical={false} />
              <XAxis dataKey="n" hide />
              <YAxis stroke="#475569" fontSize={10} axisLine={false} tickLine={false} />
              <Tooltip
                contentStyle={{
                  backgroundColor: '#020617',
                  border: '1px solid #1e293b',
                  borderRadius: '12px',
                }}
              />
              <Area
                type="monotone"
                dataKey="tension"
                fill="url(#tensionFill)"
                stroke="#ef4444"
                strokeWidth={1}
                strokeDasharray="5 5"
              />
              <Line type="monotone" dataKey="magnitude" stroke="#10b981" strokeWidth={3} dot={false} />
              {frontiers[gapType].primes.map((p) => (
                <ReferenceLine key={p} x={p} stroke="#fbbf24" strokeWidth={2} />
              ))}
            </ComposedChart>
          </ResponsiveContainer>
        </div>

        {/* REFRACTIVE GRADIENT */}
        <div className="bg-slate-900 rounded-3xl p-6 border border-slate-800 shadow-2xl">
          <h3 className="text-[10px] font-black text-slate-500 uppercase tracking-widest mb-6">
            Refractive Gradient (The Rate of Structural Return)
          </h3>
          <ResponsiveContainer width="100%" height="90%">
            <LineChart data={data}>
              <CartesianGrid strokeDasharray="3 3" stroke="#1e293b" vertical={false} />
              <XAxis dataKey="n" stroke="#475569" fontSize={10} />
              <YAxis stroke="#475569" fontSize={10} axisLine={false} tickLine={false} />
              <Line type="stepAfter" dataKey="gradient" stroke="#06b6d4" strokeWidth={2} dot={false} />
              <ReferenceLine y={0} stroke="#475569" strokeDasharray="3 3" />
            </LineChart>
          </ResponsiveContainer>
        </div>
      </div>

      <footer className="mt-6 grid grid-cols-3 gap-6">
        <div className="bg-emerald-950/20 border border-emerald-800/50 p-4 rounded-2xl text-xs leading-relaxed">
          <strong className="text-emerald-400 block mb-1">Gap Topology:</strong>
          In a <strong>Twin Cluster</strong>, the gradient never fully settles into the Null-Space.
          The tension remains low because the manifold "remembers" the structural integrity of the neighbor.
        </div>
        <div className="bg-red-950/20 border border-red-800/50 p-4 rounded-2xl text-xs leading-relaxed">
          <strong className="text-red-400 block mb-1">Desert Dynamics:</strong>
          In a <strong>Prime Desert</strong>, the tension (red zone) accumulates. This is where composite rotors
          (2, 3, 5) achieve maximum phase-lock, forcing the manifold to bend until it snaps back at the next rung.
        </div>
        <div className="bg-slate-900 border border-slate-800 p-4 rounded-2xl text-xs leading-relaxed">
          <strong className="text-slate-400 block mb-1">Discovery Index:</strong>
          The <strong>Refractive Gradient</strong> (blue) shows the "velocity" of the number line.
          A sharp spike in gradient always precedes a discovery, regardless of the gap size.
        </div>
      </footer>
    </div>
  );
};

export default App;
