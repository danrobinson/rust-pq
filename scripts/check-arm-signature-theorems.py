#!/usr/bin/env python3
"""Build and audit each host's public SHA-2 native signing session and component roots."""
from pathlib import Path
import runpy

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
profiles = [f"sha2_{bits}{speed}" for bits in (128, 192, 256) for speed in ("s", "f")]
operations = {
    "ArmKeys": ("slh_keygen_internal_spec", "keygen_spec"),
    "ArmInternal.AppleInternal": ("slh_sign_internal_spec", "slh_verify_internal_spec"),
    "ArmSdk.AppleContext.SegmentedSdk": (
        "slh_sign_spec", "slh_verify_spec", "sign_spec", "sign_deterministic_spec", "verify_spec"),
    "ArmSession": ("complete_internal", "complete", "api_complete_sign", "api_complete_sign_deterministic"),
}


def main():
    module = "Armwide.LinuxSignature"
    facade["run"](["lake", "build", module], facade["LEAN"])
    roots = [f"{owner}.slhdsa.{profile}.{operation}" for profile in profiles
             for owner, names in operations.items() for operation in names]
    roots.extend(f"NativeArmApi.{profile}.roundTrip" for profile in profiles)
    roots.extend("slhdsa.NativeArmSignature." + name for name in
                 ("slh_sign_internal_spec", "slh_verify_internal_spec"))
    for host, prefix in (("Apple", ""), ("Linux", "LinuxArmSdk.")):
        facade["audit_theorems"](module, [prefix + root for root in roots])
        print(f"{host} AArch64: audited {len(roots)} native SHA-2 API and session theorems", flush=True)


if __name__ == "__main__":
    main()
