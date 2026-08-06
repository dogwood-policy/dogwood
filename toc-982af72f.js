// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="index.html">Introduction</a></span></li><li class="chapter-item expanded "><li class="part-title">Guide</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/00-introduction.html"><strong aria-hidden="true">1.</strong> Introduction</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/01-getting-started.html"><strong aria-hidden="true">2.</strong> Getting Started</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/02-policy-language.html"><strong aria-hidden="true">3.</strong> Policy Language</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/03-event-schema.html"><strong aria-hidden="true">4.</strong> Event Schema</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/04-temporal-expressions.html"><strong aria-hidden="true">5.</strong> Temporal Expressions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/05-information-providers.html"><strong aria-hidden="true">6.</strong> Information Providers</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/06-macros.html"><strong aria-hidden="true">7.</strong> Macros</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/07-api-and-workflow.html"><strong aria-hidden="true">8.</strong> API and Workflow</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/08-formal-specification.html"><strong aria-hidden="true">9.</strong> Formal Specification</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/09-calling-macros.html"><strong aria-hidden="true">10.</strong> Calling Macros</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/10-provider-schema.html"><strong aria-hidden="true">11.</strong> Provider Schema</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/11-mcp-schema-generation.html"><strong aria-hidden="true">12.</strong> MCP Schema Generation</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="guide/12-cli.html"><strong aria-hidden="true">13.</strong> CLI</a></span></li><li class="chapter-item expanded "><li class="part-title">Examples</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/index.html"><strong aria-hidden="true">14.</strong> Examples Index</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/access_not_revoked_since_grant.html"><strong aria-hidden="true">14.1.</strong> access_not_revoked_since_grant</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_exactly_three_transfers.html"><strong aria-hidden="true">14.2.</strong> alert_exactly_three_transfers</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_heartbeat_and_login_rate.html"><strong aria-hidden="true">14.3.</strong> alert_heartbeat_and_login_rate</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_login_and_big_transfer.html"><strong aria-hidden="true">14.4.</strong> alert_login_and_big_transfer</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_login_current_tp.html"><strong aria-hidden="true">14.5.</strong> alert_login_current_tp</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_login_in_last_hour.html"><strong aria-hidden="true">14.6.</strong> alert_login_in_last_hour</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_pending_transfers.html"><strong aria-hidden="true">14.7.</strong> alert_pending_transfers</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_same_principal_login_transfer.html"><strong aria-hidden="true">14.8.</strong> alert_same_principal_login_transfer</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_same_user_login_and_transfer.html"><strong aria-hidden="true">14.9.</strong> alert_same_user_login_and_transfer</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_some_login.html"><strong aria-hidden="true">14.10.</strong> alert_some_login</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/alert_total_transfer_over_200.html"><strong aria-hidden="true">14.11.</strong> alert_total_transfer_over_200</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/allow_anything.html"><strong aria-hidden="true">14.12.</strong> allow_anything</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/approve_has_output_guard.html"><strong aria-hidden="true">14.13.</strong> approve_has_output_guard</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_cedar_macro_as_argument.html"><strong aria-hidden="true">14.14.</strong> call_cedar_macro_as_argument</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_cedar_macro_is_small.html"><strong aria-hidden="true">14.15.</strong> call_cedar_macro_is_small</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_cedar_macro_with_temporal_leaf.html"><strong aria-hidden="true">14.16.</strong> call_cedar_macro_with_temporal_leaf</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_cedar_macros_composed.html"><strong aria-hidden="true">14.17.</strong> call_cedar_macros_composed</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_temporal_aggregation_macro_count.html"><strong aria-hidden="true">14.18.</strong> call_temporal_aggregation_macro_count</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_temporal_condition_macro_once.html"><strong aria-hidden="true">14.19.</strong> call_temporal_condition_macro_once</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/call_temporal_condition_macros_composed.html"><strong aria-hidden="true">14.20.</strong> call_temporal_condition_macros_composed</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cedar_eligible_not_blocked.html"><strong aria-hidden="true">14.21.</strong> cedar_eligible_not_blocked</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cedar_is_small_threshold.html"><strong aria-hidden="true">14.22.</strong> cedar_is_small_threshold</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cedar_macro_plus_temporal_leaf.html"><strong aria-hidden="true">14.23.</strong> cedar_macro_plus_temporal_leaf</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cedar_semver_gt.html"><strong aria-hidden="true">14.24.</strong> cedar_semver_gt</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cedar_starts_with_f_like.html"><strong aria-hidden="true">14.25.</strong> cedar_starts_with_f_like</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cedar_within_cap_if_else.html"><strong aria-hidden="true">14.26.</strong> cedar_within_cap_if_else</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/cond_is_oauth_in_team.html"><strong aria-hidden="true">14.27.</strong> cond_is_oauth_in_team</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/deny_overrides_sell_not_amzn.html"><strong aria-hidden="true">14.28.</strong> deny_overrides_sell_not_amzn</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/forbid_large_except_amzn.html"><strong aria-hidden="true">14.29.</strong> forbid_large_except_amzn</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/forbid_read_transfers_over_1000.html"><strong aria-hidden="true">14.30.</strong> forbid_read_transfers_over_1000</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/get_amzn_stock_info.html"><strong aria-hidden="true">14.31.</strong> get_amzn_stock_info</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/heartbeat_scope_alias.html"><strong aria-hidden="true">14.32.</strong> heartbeat_scope_alias</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/login_attempt_custom_kind.html"><strong aria-hidden="true">14.33.</strong> login_attempt_custom_kind</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/macro_library_once_is_small.html"><strong aria-hidden="true">14.34.</strong> macro_library_once_is_small</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/max_window_raised.html"><strong aria-hidden="true">14.35.</strong> max_window_raised</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/permit_read_anyone.html"><strong aria-hidden="true">14.36.</strong> permit_read_anyone</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/principal_is_oauth.html"><strong aria-hidden="true">14.37.</strong> principal_is_oauth</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_allowed_or_short.html"><strong aria-hidden="true">14.38.</strong> provider_allowed_or_short</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_digitcount_forbid.html"><strong aria-hidden="true">14.39.</strong> provider_digitcount_forbid</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_digitcount_operator_ge.html"><strong aria-hidden="true">14.40.</strong> provider_digitcount_operator_ge</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_filter_set_index_decimal.html"><strong aria-hidden="true">14.41.</strong> provider_filter_set_index_decimal</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_int_arithmetic_trusted.html"><strong aria-hidden="true">14.42.</strong> provider_int_arithmetic_trusted</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_matches_and_not_blocked.html"><strong aria-hidden="true">14.43.</strong> provider_matches_and_not_blocked</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_principal_id_allowlist.html"><strong aria-hidden="true">14.44.</strong> provider_principal_id_allowlist</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_regex_analyze_fields.html"><strong aria-hidden="true">14.45.</strong> provider_regex_analyze_fields</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_regex_matches_uppercase.html"><strong aria-hidden="true">14.46.</strong> provider_regex_matches_uppercase</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/provider_risk_decimal_method.html"><strong aria-hidden="true">14.47.</strong> provider_risk_decimal_method</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_after_login.html"><strong aria-hidden="true">14.48.</strong> read_after_login</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_after_login_success.html"><strong aria-hidden="true">14.49.</strong> read_after_login_success</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_heartbeat_since_login_30s.html"><strong aria-hidden="true">14.50.</strong> read_heartbeat_since_login_30s</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_login_not_logout.html"><strong aria-hidden="true">14.51.</strong> read_login_not_logout</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_prev_compute_open_session.html"><strong aria-hidden="true">14.52.</strong> read_prev_compute_open_session</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_prev_login.html"><strong aria-hidden="true">14.53.</strong> read_prev_login</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_prev_login_success.html"><strong aria-hidden="true">14.54.</strong> read_prev_login_success</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/read_since_login.html"><strong aria-hidden="true">14.55.</strong> read_since_login</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_after_2024_datetime.html"><strong aria-hidden="true">14.56.</strong> sell_after_2024_datetime</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_after_approval_valid_ticker.html"><strong aria-hidden="true">14.57.</strong> sell_after_approval_valid_ticker</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_comparison_chain.html"><strong aria-hidden="true">14.58.</strong> sell_comparison_chain</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_datetime_window.html"><strong aria-hidden="true">14.59.</strong> sell_datetime_window</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_like_a_prefix.html"><strong aria-hidden="true">14.60.</strong> sell_like_a_prefix</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_logical_grouping.html"><strong aria-hidden="true">14.61.</strong> sell_logical_grouping</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_nested_if_threshold.html"><strong aria-hidden="true">14.62.</strong> sell_nested_if_threshold</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_nonzero_proceeds_decimal.html"><strong aria-hidden="true">14.63.</strong> sell_nonzero_proceeds_decimal</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_not_blocked_string.html"><strong aria-hidden="true">14.64.</strong> sell_not_blocked_string</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_not_test_tickers_like.html"><strong aria-hidden="true">14.65.</strong> sell_not_test_tickers_like</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_or_approve_action_in.html"><strong aria-hidden="true">14.66.</strong> sell_or_approve_action_in</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_shares_eq_scope.html"><strong aria-hidden="true">14.67.</strong> sell_shares_eq_scope</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_shares_temporal_subexpr.html"><strong aria-hidden="true">14.68.</strong> sell_shares_temporal_subexpr</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_small_only.html"><strong aria-hidden="true">14.69.</strong> sell_small_only</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_small_proceeds_decimal_method.html"><strong aria-hidden="true">14.70.</strong> sell_small_proceeds_decimal_method</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_threshold_by_stock.html"><strong aria-hidden="true">14.71.</strong> sell_threshold_by_stock</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_two_when_small_amzn.html"><strong aria-hidden="true">14.72.</strong> sell_two_when_small_amzn</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_unless_huge.html"><strong aria-hidden="true">14.73.</strong> sell_unless_huge</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_when_under_100.html"><strong aria-hidden="true">14.74.</strong> sell_when_under_100</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_when_unless_mix.html"><strong aria-hidden="true">14.75.</strong> sell_when_unless_mix</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/sell_zero_proceeds_if_has.html"><strong aria-hidden="true">14.76.</strong> sell_zero_proceeds_if_has</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/simplest_permit.html"><strong aria-hidden="true">14.77.</strong> simplest_permit</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/submit_after_approval_injection.html"><strong aria-hidden="true">14.78.</strong> submit_after_approval_injection</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/temporal_count_formerly_login.html"><strong aria-hidden="true">14.79.</strong> temporal_count_formerly_login</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/temporal_login_then_read.html"><strong aria-hidden="true">14.80.</strong> temporal_login_then_read</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/temporal_once_read_recent.html"><strong aria-hidden="true">14.81.</strong> temporal_once_read_recent</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/temporal_sum_formerly_transfer.html"><strong aria-hidden="true">14.82.</strong> temporal_sum_formerly_transfer</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/traders_is_in_group_scope.html"><strong aria-hidden="true">14.83.</strong> traders_is_in_group_scope</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/transfer_prev_nested_conj.html"><strong aria-hidden="true">14.84.</strong> transfer_prev_nested_conj</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/write_after_read.html"><strong aria-hidden="true">14.85.</strong> write_after_read</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="examples/write_after_read_formerly.html"><strong aria-hidden="true">14.86.</strong> write_after_read_formerly</a></span></li></ol></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split('#')[0].split('?')[0];
        if (current_page.endsWith('/')) {
            current_page += 'index.html';
        }
        const links = Array.prototype.slice.call(this.querySelectorAll('a'));
        const l = links.length;
        for (let i = 0; i < l; ++i) {
            const link = links[i];
            const href = link.getAttribute('href');
            if (href && !href.startsWith('#') && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The 'index' page is supposed to alias the first chapter in the book.
            // Check both with and without the '.html' suffix to be robust against pretty URLs
            if (link.href.replace(/\.html$/, '') === current_page.replace(/\.html$/, '')
                || i === 0
                && path_to_root === ''
                && current_page.endsWith('/index.html')) {
                link.classList.add('active');
                let parent = link.parentElement;
                while (parent) {
                    if (parent.tagName === 'LI' && parent.classList.contains('chapter-item')) {
                        parent.classList.add('expanded');
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', e => {
            if (e.target.tagName === 'A') {
                const clientRect = e.target.getBoundingClientRect();
                const sidebarRect = this.getBoundingClientRect();
                sessionStorage.setItem('sidebar-scroll-offset', clientRect.top - sidebarRect.top);
            }
        }, { passive: true });
        const sidebarScrollOffset = sessionStorage.getItem('sidebar-scroll-offset');
        sessionStorage.removeItem('sidebar-scroll-offset');
        if (sidebarScrollOffset !== null) {
            // preserve sidebar scroll position when navigating via links within sidebar
            const activeSection = this.querySelector('.active');
            if (activeSection) {
                const clientRect = activeSection.getBoundingClientRect();
                const sidebarRect = this.getBoundingClientRect();
                const currentOffset = clientRect.top - sidebarRect.top;
                this.scrollTop += currentOffset - parseFloat(sidebarScrollOffset);
            }
        } else {
            // scroll sidebar to current active section when navigating via
            // 'next/previous chapter' buttons
            const activeSection = document.querySelector('#mdbook-sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        const sidebarAnchorToggles = document.querySelectorAll('.chapter-fold-toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(el => {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define('mdbook-sidebar-scrollbox', MDBookSidebarScrollbox);


// ---------------------------------------------------------------------------
// Support for dynamically adding headers to the sidebar.

(function() {
    // This is used to detect which direction the page has scrolled since the
    // last scroll event.
    let lastKnownScrollPosition = 0;
    // This is the threshold in px from the top of the screen where it will
    // consider a header the "current" header when scrolling down.
    const defaultDownThreshold = 150;
    // Same as defaultDownThreshold, except when scrolling up.
    const defaultUpThreshold = 300;
    // The threshold is a virtual horizontal line on the screen where it
    // considers the "current" header to be above the line. The threshold is
    // modified dynamically to handle headers that are near the bottom of the
    // screen, and to slightly offset the behavior when scrolling up vs down.
    let threshold = defaultDownThreshold;
    // This is used to disable updates while scrolling. This is needed when
    // clicking the header in the sidebar, which triggers a scroll event. It
    // is somewhat finicky to detect when the scroll has finished, so this
    // uses a relatively dumb system of disabling scroll updates for a short
    // time after the click.
    let disableScroll = false;
    // Array of header elements on the page.
    let headers;
    // Array of li elements that are initially collapsed headers in the sidebar.
    // I'm not sure why eslint seems to have a false positive here.
    // eslint-disable-next-line prefer-const
    let headerToggles = [];
    // This is a debugging tool for the threshold which you can enable in the console.
    let thresholdDebug = false;

    // Updates the threshold based on the scroll position.
    function updateThreshold() {
        const scrollTop = window.pageYOffset || document.documentElement.scrollTop;
        const windowHeight = window.innerHeight;
        const documentHeight = document.documentElement.scrollHeight;

        // The number of pixels below the viewport, at most documentHeight.
        // This is used to push the threshold down to the bottom of the page
        // as the user scrolls towards the bottom.
        const pixelsBelow = Math.max(0, documentHeight - (scrollTop + windowHeight));
        // The number of pixels above the viewport, at least defaultDownThreshold.
        // Similar to pixelsBelow, this is used to push the threshold back towards
        // the top when reaching the top of the page.
        const pixelsAbove = Math.max(0, defaultDownThreshold - scrollTop);
        // How much the threshold should be offset once it gets close to the
        // bottom of the page.
        const bottomAdd = Math.max(0, windowHeight - pixelsBelow - defaultDownThreshold);
        let adjustedBottomAdd = bottomAdd;

        // Adjusts bottomAdd for a small document. The calculation above
        // assumes the document is at least twice the windowheight in size. If
        // it is less than that, then bottomAdd needs to be shrunk
        // proportional to the difference in size.
        if (documentHeight < windowHeight * 2) {
            const maxPixelsBelow = documentHeight - windowHeight;
            const t = 1 - pixelsBelow / Math.max(1, maxPixelsBelow);
            const clamp = Math.max(0, Math.min(1, t));
            adjustedBottomAdd *= clamp;
        }

        let scrollingDown = true;
        if (scrollTop < lastKnownScrollPosition) {
            scrollingDown = false;
        }

        if (scrollingDown) {
            // When scrolling down, move the threshold up towards the default
            // downwards threshold position. If near the bottom of the page,
            // adjustedBottomAdd will offset the threshold towards the bottom
            // of the page.
            const amountScrolledDown = scrollTop - lastKnownScrollPosition;
            const adjustedDefault = defaultDownThreshold + adjustedBottomAdd;
            threshold = Math.max(adjustedDefault, threshold - amountScrolledDown);
        } else {
            // When scrolling up, move the threshold down towards the default
            // upwards threshold position. If near the bottom of the page,
            // quickly transition the threshold back up where it normally
            // belongs.
            const amountScrolledUp = lastKnownScrollPosition - scrollTop;
            const adjustedDefault = defaultUpThreshold - pixelsAbove
                + Math.max(0, adjustedBottomAdd - defaultDownThreshold);
            threshold = Math.min(adjustedDefault, threshold + amountScrolledUp);
        }

        if (documentHeight <= windowHeight) {
            threshold = 0;
        }

        if (thresholdDebug) {
            const id = 'mdbook-threshold-debug-data';
            let data = document.getElementById(id);
            if (data === null) {
                data = document.createElement('div');
                data.id = id;
                data.style.cssText = `
                    position: fixed;
                    top: 50px;
                    right: 10px;
                    background-color: 0xeeeeee;
                    z-index: 9999;
                    pointer-events: none;
                `;
                document.body.appendChild(data);
            }
            data.innerHTML = `
                <table>
                  <tr><td>documentHeight</td><td>${documentHeight.toFixed(1)}</td></tr>
                  <tr><td>windowHeight</td><td>${windowHeight.toFixed(1)}</td></tr>
                  <tr><td>scrollTop</td><td>${scrollTop.toFixed(1)}</td></tr>
                  <tr><td>pixelsAbove</td><td>${pixelsAbove.toFixed(1)}</td></tr>
                  <tr><td>pixelsBelow</td><td>${pixelsBelow.toFixed(1)}</td></tr>
                  <tr><td>bottomAdd</td><td>${bottomAdd.toFixed(1)}</td></tr>
                  <tr><td>adjustedBottomAdd</td><td>${adjustedBottomAdd.toFixed(1)}</td></tr>
                  <tr><td>scrollingDown</td><td>${scrollingDown}</td></tr>
                  <tr><td>threshold</td><td>${threshold.toFixed(1)}</td></tr>
                </table>
            `;
            drawDebugLine();
        }

        lastKnownScrollPosition = scrollTop;
    }

    function drawDebugLine() {
        if (!document.body) {
            return;
        }
        const id = 'mdbook-threshold-debug-line';
        const existingLine = document.getElementById(id);
        if (existingLine) {
            existingLine.remove();
        }
        const line = document.createElement('div');
        line.id = id;
        line.style.cssText = `
            position: fixed;
            top: ${threshold}px;
            left: 0;
            width: 100vw;
            height: 2px;
            background-color: red;
            z-index: 9999;
            pointer-events: none;
        `;
        document.body.appendChild(line);
    }

    function mdbookEnableThresholdDebug() {
        thresholdDebug = true;
        updateThreshold();
        drawDebugLine();
    }

    window.mdbookEnableThresholdDebug = mdbookEnableThresholdDebug;

    // Updates which headers in the sidebar should be expanded. If the current
    // header is inside a collapsed group, then it, and all its parents should
    // be expanded.
    function updateHeaderExpanded(currentA) {
        // Add expanded to all header-item li ancestors.
        let current = currentA.parentElement;
        while (current) {
            if (current.tagName === 'LI' && current.classList.contains('header-item')) {
                current.classList.add('expanded');
            }
            current = current.parentElement;
        }
    }

    // Updates which header is marked as the "current" header in the sidebar.
    // This is done with a virtual Y threshold, where headers at or below
    // that line will be considered the current one.
    function updateCurrentHeader() {
        if (!headers || !headers.length) {
            return;
        }

        // Reset the classes, which will be rebuilt below.
        const els = document.getElementsByClassName('current-header');
        for (const el of els) {
            el.classList.remove('current-header');
        }
        for (const toggle of headerToggles) {
            toggle.classList.remove('expanded');
        }

        // Find the last header that is above the threshold.
        let lastHeader = null;
        for (const header of headers) {
            const rect = header.getBoundingClientRect();
            if (rect.top <= threshold) {
                lastHeader = header;
            } else {
                break;
            }
        }
        if (lastHeader === null) {
            lastHeader = headers[0];
            const rect = lastHeader.getBoundingClientRect();
            const windowHeight = window.innerHeight;
            if (rect.top >= windowHeight) {
                return;
            }
        }

        // Get the anchor in the summary.
        const href = '#' + lastHeader.id;
        const a = [...document.querySelectorAll('.header-in-summary')]
            .find(element => element.getAttribute('href') === href);
        if (!a) {
            return;
        }

        a.classList.add('current-header');

        updateHeaderExpanded(a);
    }

    // Updates which header is "current" based on the threshold line.
    function reloadCurrentHeader() {
        if (disableScroll) {
            return;
        }
        updateThreshold();
        updateCurrentHeader();
    }


    // When clicking on a header in the sidebar, this adjusts the threshold so
    // that it is located next to the header. This is so that header becomes
    // "current".
    function headerThresholdClick(event) {
        // See disableScroll description why this is done.
        disableScroll = true;
        setTimeout(() => {
            disableScroll = false;
        }, 100);
        // requestAnimationFrame is used to delay the update of the "current"
        // header until after the scroll is done, and the header is in the new
        // position.
        requestAnimationFrame(() => {
            requestAnimationFrame(() => {
                // Closest is needed because if it has child elements like <code>.
                const a = event.target.closest('a');
                const href = a.getAttribute('href');
                const targetId = href.substring(1);
                const targetElement = document.getElementById(targetId);
                if (targetElement) {
                    threshold = targetElement.getBoundingClientRect().bottom;
                    updateCurrentHeader();
                }
            });
        });
    }

    // Takes the nodes from the given head and copies them over to the
    // destination, along with some filtering.
    function filterHeader(source, dest) {
        const clone = source.cloneNode(true);
        clone.querySelectorAll('mark').forEach(mark => {
            mark.replaceWith(...mark.childNodes);
        });
        dest.append(...clone.childNodes);
    }

    // Scans page for headers and adds them to the sidebar.
    document.addEventListener('DOMContentLoaded', function() {
        const activeSection = document.querySelector('#mdbook-sidebar .active');
        if (activeSection === null) {
            return;
        }

        const main = document.getElementsByTagName('main')[0];
        headers = Array.from(main.querySelectorAll('h2, h3, h4, h5, h6'))
            .filter(h => h.id !== '' && h.children.length && h.children[0].tagName === 'A');

        if (headers.length === 0) {
            return;
        }

        // Build a tree of headers in the sidebar.

        const stack = [];

        const firstLevel = parseInt(headers[0].tagName.charAt(1));
        for (let i = 1; i < firstLevel; i++) {
            const ol = document.createElement('ol');
            ol.classList.add('section');
            if (stack.length > 0) {
                stack[stack.length - 1].ol.appendChild(ol);
            }
            stack.push({level: i + 1, ol: ol});
        }

        // The level where it will start folding deeply nested headers.
        const foldLevel = 3;

        for (let i = 0; i < headers.length; i++) {
            const header = headers[i];
            const level = parseInt(header.tagName.charAt(1));

            const currentLevel = stack[stack.length - 1].level;
            if (level > currentLevel) {
                // Begin nesting to this level.
                for (let nextLevel = currentLevel + 1; nextLevel <= level; nextLevel++) {
                    const ol = document.createElement('ol');
                    ol.classList.add('section');
                    const last = stack[stack.length - 1];
                    const lastChild = last.ol.lastChild;
                    // Handle the case where jumping more than one nesting
                    // level, which doesn't have a list item to place this new
                    // list inside of.
                    if (lastChild) {
                        lastChild.appendChild(ol);
                    } else {
                        last.ol.appendChild(ol);
                    }
                    stack.push({level: nextLevel, ol: ol});
                }
            } else if (level < currentLevel) {
                while (stack.length > 1 && stack[stack.length - 1].level > level) {
                    stack.pop();
                }
            }

            const li = document.createElement('li');
            li.classList.add('header-item');
            li.classList.add('expanded');
            if (level < foldLevel) {
                li.classList.add('expanded');
            }
            const span = document.createElement('span');
            span.classList.add('chapter-link-wrapper');
            const a = document.createElement('a');
            span.appendChild(a);
            a.href = '#' + header.id;
            a.classList.add('header-in-summary');
            filterHeader(header.children[0], a);
            a.addEventListener('click', headerThresholdClick);
            const nextHeader = headers[i + 1];
            if (nextHeader !== undefined) {
                const nextLevel = parseInt(nextHeader.tagName.charAt(1));
                if (nextLevel > level && level >= foldLevel) {
                    const toggle = document.createElement('a');
                    toggle.classList.add('chapter-fold-toggle');
                    toggle.classList.add('header-toggle');
                    toggle.addEventListener('click', () => {
                        li.classList.toggle('expanded');
                    });
                    const toggleDiv = document.createElement('div');
                    toggleDiv.textContent = '❱';
                    toggle.appendChild(toggleDiv);
                    span.appendChild(toggle);
                    headerToggles.push(li);
                }
            }
            li.appendChild(span);

            const currentParent = stack[stack.length - 1];
            currentParent.ol.appendChild(li);
        }

        const onThisPage = document.createElement('div');
        onThisPage.classList.add('on-this-page');
        onThisPage.append(stack[0].ol);
        const activeItemSpan = activeSection.parentElement;
        activeItemSpan.after(onThisPage);
    });

    document.addEventListener('DOMContentLoaded', reloadCurrentHeader);
    document.addEventListener('scroll', reloadCurrentHeader, { passive: true });
})();

