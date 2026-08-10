"""
The Music of the Zeros: Mapping Deninger's Frequencies to the Fretboard
"""

import sys
import math
from mpmath import mp

# We port the core music theory concepts from fretboard-mapper
NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']

def hz_to_midi(freq_hz):
    # MIDI 69 is A4 = 440Hz
    return 69 + 12 * math.log2(freq_hz / 440.0)

def midi_to_note_name(midi_val):
    midi_rounded = int(round(midi_val))
    degree = midi_rounded % 12
    octave = midi_rounded // 12 - 1
    return f"{NOTE_NAMES[degree]}{octave}", NOTE_NAMES[degree]

def analyze_spectrum(name, gammas, base_midi=40):
    # Map the first zero to the base_midi (e.g., 40 = E2, low string of guitar)
    print(f"\n{'='*60}")
    print(f"🎵 Spectrum Analysis: {name}")
    print(f"{'='*60}")
    
    if not gammas:
        print("No frequencies to analyze.")
        return
        
    base_gamma = float(gammas[0])
    
    notes_in_scale = set()
    
    for i, g in enumerate(gammas):
        # We treat gamma as a frequency and transpose it so gamma_1 = base_midi
        # ratio = g / base_gamma
        # midi = base_midi + 12 * log2(ratio)
        ratio = float(g) / base_gamma
        midi_val = base_midi + 12 * math.log2(ratio)
        
        full_note, note_class = midi_to_note_name(midi_val)
        notes_in_scale.add(note_class)
        
        cents_off = (midi_val - round(midi_val)) * 100
        
        if i < 10:
            print(f"Zero {i+1:2d} (γ = {float(g):7.3f}) -> {full_note:>4} {cents_off:+5.1f} cents")
            
    # Print the resulting scale
    sorted_scale = []
    for n in NOTE_NAMES:
        if n in notes_in_scale:
            sorted_scale.append(n)
            
    print(f"\nTotal unique pitch classes in the first {len(gammas)} zeros: {len(notes_in_scale)}")
    print(f"Scale Pitch Classes: {' - '.join(sorted_scale)}")

if __name__ == "__main__":
    # 1. Zeros of the Riemann Zeta Function
    from zeta.zeros import first_n_zeros
    zeta_gammas = first_n_zeros(50)
    
    # 2. Zeros of the Davenport-Heilbronn Function
    from zeta.epstein import Z_dh
    mp.dps = 15
    print("Finding the first 50 zeros of Davenport-Heilbronn...")
    dh_gammas = []
    t = mp.mpf(0.1)
    step = 0.25
    prev_Z = Z_dh(t)
    while len(dh_gammas) < 50:
        t += step
        cur_Z = Z_dh(t)
        if prev_Z != 0 and cur_Z != 0 and (prev_Z > 0) != (cur_Z > 0):
            root = mp.findroot(lambda x: Z_dh(x), (t - step, t), solver='secant')
            dh_gammas.append(root)
        prev_Z = cur_Z
        
    # Analyze them! We'll map the first zero to E2 (MIDI 40)
    analyze_spectrum("Riemann Zeta Function", zeta_gammas, base_midi=40)
    analyze_spectrum("Davenport-Heilbronn (The Imposter)", dh_gammas, base_midi=40)
