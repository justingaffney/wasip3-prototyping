use core::future::Future;
use core::time::Duration;

use cap_std::time::SystemTime;
use tokio::time::sleep;
use wasmtime::component::Accessor;

use crate::p3::bindings::clocks::{monotonic_clock, wall_clock};
use crate::p3::clocks::{WasiClocksImpl, WasiClocksView};

impl TryFrom<SystemTime> for wall_clock::Datetime {
    type Error = wasmtime::Error;

    fn try_from(time: SystemTime) -> Result<Self, Self::Error> {
        let duration =
            time.duration_since(SystemTime::from_std(std::time::SystemTime::UNIX_EPOCH))?;

        Ok(Self {
            seconds: duration.as_secs(),
            nanoseconds: duration.subsec_nanos(),
        })
    }
}

impl<T> wall_clock::Host for WasiClocksImpl<&mut T>
where
    T: WasiClocksView,
{
    fn now(&mut self) -> wasmtime::Result<wall_clock::Datetime> {
        let now = self.clocks().wall_clock.now();
        Ok(wall_clock::Datetime {
            seconds: now.as_secs(),
            nanoseconds: now.subsec_nanos(),
        })
    }

    fn resolution(&mut self) -> wasmtime::Result<wall_clock::Datetime> {
        let res = self.clocks().wall_clock.resolution();
        Ok(wall_clock::Datetime {
            seconds: res.as_secs(),
            nanoseconds: res.subsec_nanos(),
        })
    }
}

impl<T> monotonic_clock::Host for WasiClocksImpl<&mut T>
where
    T: WasiClocksView,
{
    type Data = T;

    fn now(&mut self) -> wasmtime::Result<monotonic_clock::Instant> {
        Ok(self.clocks().monotonic_clock.now())
    }

    fn resolution(&mut self) -> wasmtime::Result<monotonic_clock::Instant> {
        Ok(self.clocks().monotonic_clock.resolution())
    }

    fn wait_until(
        store: &mut Accessor<Self::Data>,
        when: monotonic_clock::Instant,
    ) -> impl Future<Output = wasmtime::Result<()>> {
        let clock_now = store.with(|store| store.data().clocks().monotonic_clock.now());
        async move {
            if when > clock_now {
                sleep(Duration::from_nanos(when - clock_now)).await;
            };
            Ok(())
        }
    }

    fn wait_for(
        _store: &mut Accessor<Self::Data>,
        duration: monotonic_clock::Duration,
    ) -> impl Future<Output = wasmtime::Result<()>> {
        async move {
            if duration > 0 {
                sleep(Duration::from_nanos(duration)).await;
            }
            Ok(())
        }
    }
}
