#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GcCollectionKind {
    Minor,
    Major,
}

impl GcCollectionKind {
    pub fn as_str(self) -> &'static str {
        match self {
            GcCollectionKind::Minor => "minor",
            GcCollectionKind::Major => "major",
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct GcCycleReport {
    pub kind: Option<GcCollectionKind>,
    pub marked_nodes: usize,
    pub freed_nodes: usize,
    pub promoted_nodes: usize,
    pub live_nodes_before: usize,
    pub live_nodes_after: usize,
    pub young_live_before: usize,
    pub young_live_after: usize,
    pub old_live_before: usize,
    pub old_live_after: usize,
    pub elapsed_sec: f64,
    pub worker_threads: usize,
}

#[derive(Debug, Clone)]
pub struct GcRuntimeStats {
    pub total_collections: u64,
    pub minor_collections: u64,
    pub major_collections: u64,
    pub auto_triggers: u64,
    pub manual_triggers: u64,
    pub minor_since_major: u64,
    pub major_every_minor: u64,
    pub old_generation_soft_limit: usize,
    pub total_gc_time_sec: f64,
    pub total_nodes_freed: usize,
    pub total_nodes_promoted: usize,
    pub last_pause_sec: f64,
    pub last_collection_kind: Option<GcCollectionKind>,
    pub last_marked_nodes: usize,
    pub last_freed_nodes: usize,
    pub last_promoted_nodes: usize,
    pub last_live_nodes: usize,
    pub last_young_live_nodes: usize,
    pub last_old_live_nodes: usize,
    pub max_parallel_workers_observed: usize,
}

impl Default for GcRuntimeStats {
    fn default() -> Self {
        Self {
            total_collections: 0,
            minor_collections: 0,
            major_collections: 0,
            auto_triggers: 0,
            manual_triggers: 0,
            minor_since_major: 0,
            major_every_minor: 8,
            old_generation_soft_limit: 120_000,
            total_gc_time_sec: 0.0,
            total_nodes_freed: 0,
            total_nodes_promoted: 0,
            last_pause_sec: 0.0,
            last_collection_kind: None,
            last_marked_nodes: 0,
            last_freed_nodes: 0,
            last_promoted_nodes: 0,
            last_live_nodes: 0,
            last_young_live_nodes: 0,
            last_old_live_nodes: 0,
            max_parallel_workers_observed: 0,
        }
    }
}

impl GcRuntimeStats {
    pub fn record_cycle(&mut self, report: &GcCycleReport, manual_trigger: bool) {
        let Some(kind) = report.kind else {
            return;
        };
        self.total_collections = self.total_collections.saturating_add(1);
        match kind {
            GcCollectionKind::Minor => {
                self.minor_collections = self.minor_collections.saturating_add(1);
                self.minor_since_major = self.minor_since_major.saturating_add(1);
            }
            GcCollectionKind::Major => {
                self.major_collections = self.major_collections.saturating_add(1);
                self.minor_since_major = 0;
            }
        }
        if manual_trigger {
            self.manual_triggers = self.manual_triggers.saturating_add(1);
        } else {
            self.auto_triggers = self.auto_triggers.saturating_add(1);
        }
        self.total_gc_time_sec += report.elapsed_sec;
        self.total_nodes_freed = self.total_nodes_freed.saturating_add(report.freed_nodes);
        self.total_nodes_promoted =
            self.total_nodes_promoted.saturating_add(report.promoted_nodes);
        self.last_pause_sec = report.elapsed_sec;
        self.last_collection_kind = Some(kind);
        self.last_marked_nodes = report.marked_nodes;
        self.last_freed_nodes = report.freed_nodes;
        self.last_promoted_nodes = report.promoted_nodes;
        self.last_live_nodes = report.live_nodes_after;
        self.last_young_live_nodes = report.young_live_after;
        self.last_old_live_nodes = report.old_live_after;
        if report.worker_threads > self.max_parallel_workers_observed {
            self.max_parallel_workers_observed = report.worker_threads;
        }
    }
}
