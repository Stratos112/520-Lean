# Sky Vercauteren
# A stupid little inverse fourier transform for testing


import math
import sys
import ast

# now accepts form [ (R, I), ... ]
def inverse_dft(waves):
    samples = []
    N = len(waves)
    eul = 0
    for n in range(N):
        for k in range(N):
            R, I = waves[k]
            X = complex(R, I)
            theta = ((2 * 3.141592653589793 * n * k)/N)
            exp = math.cos(theta) + 1j * math.sin(theta)
            eul += X * exp
            real = round(eul.real/N, 4)
        
        samples.append(real)
        eul = 0
    return samples

def conjugate_cosine(amps):
    N = len(amps)
    X = [(0.0, 0.0)] * N
    en_amps = enumerate(amps)
    for k, a in en_amps:
        if a == 0:
            continue
        # this is the conjugate part. 
        if k == 0 or 2 * k == N:    
            #treat everything like a cosine. we can make a similar method for sine 
            X[k] = (a * N, 0.0)
        elif 2 * k < N:
            X[k] = (a * N / 2, 0.0)
            X[N - k] = (a * N / 2, 0.0)  # partner
    return X

def format_out(input, output):
    return f"#eval DFT {len(input)} (#v{output}) -- expect {input}"

if __name__ == "__main__":
    if len(sys.argv) < 2:
        #default = [(6,0),(0,0),(0,0),(1,0), (0,0), (0,0) ,(0,0), (0,0)]
        #default = [(8,0),(0,0),(4,0),(0,0), (0,0), (0,0) ,(4,0), (0,0)]
        default = conjugate_cosine([0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0])

        out = inverse_dft(default)
        print(format_out(default, out))
    else:
        waves = ast.literal_eval(sys.argv[1])

        out = inverse_dft(waves)
        print(format_out(waves, out))
    sys.exit()