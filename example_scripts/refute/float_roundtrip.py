# True over exact rationals, false in IEEE doubles: 1.0 / 49 * 49 == 0.9999999999999999. A proof of
# this property in the provable twin (ℚ) would say nothing about the float program.
def roundtrip(x: float) -> float:
    return x / 49 * 49


def roundtrip_identity(x: float):
    assert roundtrip(x) == x
