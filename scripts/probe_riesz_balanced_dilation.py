"""Failed-candidate diagnostic; not a floor certificate or actual-prime sum.

Use the literal moving length and balanced-pair coefficient in log
coordinates. Keep its exact radial factorial weight and entire character.
Only common positive/phase factors cancel in normalized Gram correlations.
The grid is NOT claimed to be a prime-density transport.
"""
import json
import math
from pathlib import Path
import numpy as np

U = 10001/20000
TARGET = 399/5000


def profile(N, height, order):
    nodes, quad = np.polynomial.legendre.leggauss(order)
    a = (nodes+1)/2
    x = N+a[:, None]
    b = (nodes+1)/2
    z = N+1+b[None, :]
    T = x+z
    # The exact damped floor length differs by at most this enclosure.
    logA = N*math.log(1/U)-math.log(N+1)
    L = 2*logA
    logFloorLengthError = math.log(4)-logA
    assert np.all(x<L) and np.all(z<L) and np.all(T>L)
    # Original correction and SAME head fail their >=1.02N owner mask.
    assert float(x.max()) < 1.02*N and float(z.max()) < 1.02*N
    assert float(T.min()) > 1.971*N+1
    assert float(T.max()) < 2.029*N-1
    defect = -T*(T-L)/L+2*x*z/T
    assert np.all(defect >= N/20)
    mid = 2*N+2
    radial = np.exp(N*np.log1p((T-mid)/mid)-1.5*(T-mid))
    amp = (defect/N)*radial
    # Remove the one COMMON phase exp(-iy(2N+1)); it cancels in Gram.
    phase = np.exp(-1j*height*(a[:, None]+b[None, :]))
    weighted = amp*phase*np.sqrt(quad[None, :]/2)
    gram = weighted @ weighted.conj().T
    realgram = (amp*(quad[None, :]/2)) @ amp.T
    expected = np.exp(-1j*height*(a[:, None]-a[None, :]))*realgram
    exact_error = float(np.max(np.abs(gram-expected)) / np.max(realgram))
    energy = np.diag(realgram)
    correlation = np.abs(gram)/np.sqrt(energy[:, None]*energy[None, :])
    eig = np.linalg.eigvalsh(realgram)
    trace = float(eig.sum())
    return {
        'N': N, 'height': height, 'gridOrder': order,
        'movingLengthLower': L,
        'logFloorLengthRoundingErrorUpper': logFloorLengthError,
        'allActualBalancedMasksPreservedInCoefficientFormula': True,
        'minimumDefectOverN': float(defect.min()/N),
        'constantPhaseGramRelativeError': exact_error,
        'minimumNormalizedRowCorrelation': float(correlation.min()),
        'largestGramEigenvalueFraction': float(eig[-1]/trace),
        'effectiveGramRank': trace*trace/float(np.dot(eig,eig)),
        'actualPrimeEnumeration': False,
        'arithmeticDensityTransport': False,
        'independentFloorBound': False,
        'savingCreditedAgainstTarget': 0,
    }


rows = [profile(N, y, order)
        for N in [65536, 90112, 196608, 425984, 917504, 1966080, 4194304]
        for y in [54, 100]
        for order in [32, 64]]
source = 1-math.log(32/13)/(-2*U*math.log(U))+math.log(19/13)
report = {
    'scope': 'Failed orthogonality candidate; quantitative model diagnostic only',
    'target': TARGET, 'existingSource': source,
    'unchangedSourceGap': source-TARGET,
    'signedBalancedPairMilestoneAchieved': False,
    'rows': rows,
}
path = Path('.lake/riesz-balanced-dilation-audit/numerics.json')
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
print(json.dumps({
    'rows': len(rows),
    'maxIdentityError': max(r['constantPhaseGramRelativeError'] for r in rows),
    'minCorrelation': min(r['minimumNormalizedRowCorrelation'] for r in rows),
    'maxEffectiveRank': max(r['effectiveGramRank'] for r in rows),
    'targetSaving': 0,
    'sourceGap': source-TARGET,
}, sort_keys=True))
