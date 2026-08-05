"""
Discovery Lab 8: The Acoustic Interference of the Riemann Zeros

We will physically synthesize the Riemann zeros into an audio file (.wav).
By mapping the imaginary parts (gammas) to Hz, we can listen to the "chord" 
of the Riemann Zeta function and hear the wave interference ("beats").

The explicit formula involves terms like x^(i*gamma) = cos(gamma * ln(x)).
If we map this to time 't', the waves are actually "chirps" (sweeping frequencies),
but to hear the pure harmony, we will first just treat them as constant frequencies.
"""

import numpy as np
from scipy.io.wavfile import write
from zeta.zeros import first_n_zeros

def generate_riemann_audio(num_zeros=20, duration=5.0, sample_rate=44100):
    print(f"Fetching the first {num_zeros} Riemann zeros...")
    target_zeros = [float(z) for z in first_n_zeros(num_zeros)]
    
    # We create an array of time values
    t = np.linspace(0, duration, int(sample_rate * duration), False)
    
    # We will build up the audio signal by adding the waves together
    # Initialize an empty array for the composite wave
    composite_wave = np.zeros_like(t)
    
    print("Synthesizing the acoustic waves...")
    
    for i, gamma in enumerate(target_zeros):
        # The gammas start at 14.13. As Hz, this is very low (sub-bass).
        # We will multiply by a scalar (e.g., 20) to put it into the audible midrange.
        frequency_hz = gamma * 10.0 
        
        print(f"Zero {i+1:2d}: {gamma:7.3f} -> {frequency_hz:7.1f} Hz")
        
        # Generate the sine wave for this zero
        # We use a slight amplitude decay for higher zeros (1 / gamma) to mimic natural harmonics
        amplitude = 1.0 / (gamma ** 0.5) 
        wave = amplitude * np.sin(2 * np.pi * frequency_hz * t)
        
        # Add to the master mix (Wave Interference!)
        composite_wave += wave

    # Normalize the audio to 16-bit PCM format (-32768 to 32767)
    max_amp = np.max(np.abs(composite_wave))
    normalized_wave = np.int16((composite_wave / max_amp) * 32767)
    
    # Write to a file
    filename = "riemann_interference_beats.wav"
    write(filename, sample_rate, normalized_wave)
    print(f"\n✅ Audio generated successfully: {filename}")
    print("You can now physically listen to the Riemann zeros interfering with each other!")

if __name__ == "__main__":
    generate_riemann_audio(num_zeros=30, duration=10.0)
