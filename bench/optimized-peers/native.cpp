#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <span>
#include <stdexcept>
#include <string>
#include <vector>
#ifdef FLUHRER
#include "api.h"
#else
#include <botan/pubkey.h>
#include <botan/rng.h>
#include <botan/sphincsplus.h>
#endif

using Bytes = std::vector<uint8_t>;
using Clock = std::chrono::steady_clock;
static void check(bool ok) {
    if (!ok)
        throw std::runtime_error("operation failed");
}
static int round_id;

template <class F> auto measure(const std::string &set, const char *op, int count, F f) {
    const auto start = Clock::now();
    for (int i = 1; i < count; ++i)
        f();
    auto result = f();
    const auto elapsed =
        std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start).count();
    std::cout << set << ',' << op << ',' << round_id << ',' << elapsed / count << '\n';
    return result;
}

static void save(const std::string &set, const char *suffix, std::span<const uint8_t> bytes) {
    std::ofstream file(std::string(std::getenv("SLH_VECTORS")) + "/" + set + "." + suffix,
                       std::ios::binary);
    file.write(reinterpret_cast<const char *>(bytes.data()), bytes.size());
    check(file.good());
}

// Deterministic public benchmark inputs. Each provider consumes the same bytes.
static bool hedging;
static size_t offset;
static uint8_t next_byte() {
    if (hedging)
        return 123 ^ round_id;
    return static_cast<uint8_t>(42 + round_id + offset++);
}

#ifdef FLUHRER
static bool fill(void *ptr, size_t len) {
    std::generate_n(static_cast<uint8_t *>(ptr), len, next_byte);
    return true;
}
static std::unique_ptr<slh_dsa::key> key_for(const std::string &set) {
#define KEY(s)                                                                                          \
    if (set == #s)                                                                                      \
    return std::make_unique<slh_dsa::key_##s>()
    KEY(sha2_128s);
    KEY(sha2_128f);
    KEY(sha2_192s);
    KEY(sha2_192f);
    KEY(sha2_256s);
    KEY(sha2_256f);
    KEY(shake_128s);
    KEY(shake_128f);
    KEY(shake_192s);
    KEY(shake_192f);
    KEY(shake_256s);
    KEY(shake_256f);
#undef KEY
    throw std::invalid_argument(set);
}
#else
class BenchRng final : public Botan::RandomNumberGenerator {
    void fill_bytes_with_input(std::span<uint8_t> out, std::span<const uint8_t>) override {
        std::generate(out.begin(), out.end(), ::next_byte);
    }
    bool accepts_input() const override { return false; }
    bool is_seeded() const override { return true; }
    std::string name() const override { return "benchmark"; }
    void clear() override {}
};
#endif

int main(int argc, char **argv) {
    check(argc >= 3);
    round_id = std::stoi(argv[1]);
    Bytes msg(std::stoul(argv[2]), 17 ^ round_id);
    for (std::string family : {"sha2", "shake"})
        for (std::string param : {"128s", "128f", "192s", "192f", "256s", "256f"}) {
            const auto set = family + "_" + param;
            hedging = false;
            offset = 0;
#ifdef FLUHRER
            auto key = key_for(set);
            key->set_num_thread(std::stoul(argv[3]));
            measure(set, "keygen", 1, [&] {
                check(key->generate_key_pair(fill));
                return true;
            });
            const auto *sk = key->get_private_key();
            save(set, "sk", {sk, key->len_private_key()});
            auto pk = measure(set, "public_key", 256, [&] {
                auto p = key->get_public_key();
                return Bytes(p, p + key->len_public_key());
            });
            auto sign = [&](bool randomized) {
                Bytes out(key->len_signature());
                check(key->sign(out.data(), out.size(), msg.data(), msg.size(), nullptr, 0,
                                randomized ? fill : nullptr));
                return out;
            };
#else
            BenchRng rng;
            const auto params = Botan::Sphincs_Parameters::create(
                "SLH-DSA-" + std::string(family == "sha2" ? "SHA2" : "SHAKE") + "-" + param);
            auto key =
                measure(set, "keygen", 1, [&] { return Botan::SphincsPlus_PrivateKey(rng, params); });
            save(set, "sk", key.raw_private_key_bits());
            auto pk = measure(set, "public_key", 256, [&] { return key.raw_public_key_bits(); });
            auto sign = [&](bool randomized) {
                Botan::PK_Signature_Options opts;
                if (!randomized)
                    opts = opts.with_deterministic_signature();
                Botan::PK_Signer signer(key, rng, opts);
                return signer.sign_message(msg, rng);
            };
#endif
            save(set, "pk", pk);
            const auto sig = measure(set, "sign", 1, [&] { return sign(false); });
            hedging = true;
            const auto randomized = measure(set, "sign_hedged", 1, [&] { return sign(true); });
            save(set, "sig", sig);
            save(set, "hedged", randomized);
            auto verify = [&] {
#ifdef FLUHRER
                return key->verify(sig.data(), sig.size(), msg.data(), msg.size());
#else
                Botan::PK_Verifier verifier(key);
                return verifier.verify_message(msg, sig);
#endif
            };
            measure(set, "verify", 32, [&] {
                check(verify());
                return true;
            });
            msg[0] ^= 1;
            check(!verify());
            msg[0] ^= 1;
        }
}
