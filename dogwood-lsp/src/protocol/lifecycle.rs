#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum Lifecycle {
    #[default]
    PreInitialize,
    AwaitInitialized,
    Running,
    Shutdown,
}

impl Lifecycle {
    pub(crate) fn begin_initialization(&mut self) {
        debug_assert_eq!(*self, Self::PreInitialize);
        *self = Self::AwaitInitialized;
    }

    pub(crate) fn initialized(&mut self) {
        debug_assert_eq!(*self, Self::AwaitInitialized);
        *self = Self::Running;
    }

    pub(crate) fn shutdown(&mut self) {
        debug_assert_eq!(*self, Self::Running);
        *self = Self::Shutdown;
    }

    pub(crate) const fn exit_code(self) -> u8 {
        if matches!(self, Self::Shutdown) { 0 } else { 1 }
    }
}

// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#[cfg(all(test, unix))]
mod tests {
    use super::Lifecycle;

    #[test]
    fn lifecycle_follows_the_required_state_order() {
        let mut lifecycle = Lifecycle::default();
        assert_eq!(lifecycle, Lifecycle::PreInitialize);

        lifecycle.begin_initialization();
        assert_eq!(lifecycle, Lifecycle::AwaitInitialized);

        lifecycle.initialized();
        assert_eq!(lifecycle, Lifecycle::Running);

        lifecycle.shutdown();
        assert_eq!(lifecycle, Lifecycle::Shutdown);
    }

    #[test]
    fn exit_succeeds_only_after_shutdown() {
        assert_eq!(Lifecycle::PreInitialize.exit_code(), 1);
        assert_eq!(Lifecycle::AwaitInitialized.exit_code(), 1);
        assert_eq!(Lifecycle::Running.exit_code(), 1);
        assert_eq!(Lifecycle::Shutdown.exit_code(), 0);
    }
}
