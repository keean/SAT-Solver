//----------------------------------------------------------------------------
// copyright 2012, 2013, 2014 Keean Schupke
// compile with g++ -std=gnu++11 
// profile.hpp

inline uint64_t rtime() {
    struct rusage rusage;
    getrusage(RUSAGE_SELF, &rusage);
    return 1000000 * static_cast<uint64_t>(rusage.ru_utime.tv_sec)
        + static_cast<uint64_t>(rusage.ru_utime.tv_usec);
}

class profile {
    static uint64_t t;
    static uint64_t s;

public:
    profile() {
        s = rtime();
    }

    ~profile() {
        t += rtime() - s;
    }

    static void start() {
        s = rtime();
    }

    static void finish() {
        t += rtime() - s;
    }

    static uint64_t report() {
        uint64_t r = t;
        t = 0;
        return r;
    }
};

uint64_t profile::t {0};
uint64_t profile::s;

