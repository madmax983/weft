//! Semantic controls for the Weft ECS example.
//! Timings compare two native Rust implementations, not Rust with interpreted Weft.

use std::hint::black_box;
use std::time::{Duration, Instant};

use bevy_ecs::prelude::*;
use bevy_ecs::schedule::SingleThreadedExecutor;

#[derive(Component, Clone, Copy)]
struct Position {
    x: i64,
    y: i64,
}

#[derive(Component, Clone, Copy)]
struct Velocity {
    x: i64,
    y: i64,
}

#[derive(Component, Clone, Copy)]
struct Health {
    hp: i64,
}

fn movement(mut query: Query<(&mut Position, &Velocity)>) {
    for (mut p, v) in &mut query {
        p.x += v.x;
        p.y += v.y;
    }
}

fn damage(mut query: Query<&mut Health>) {
    for mut h in &mut query {
        h.hp -= 1;
    }
}

fn bevy(n: i64, ticks: i64) -> (i64, Duration) {
    let mut world = World::new();
    for i in 0..n {
        let p = Position { x: i, y: 2 * i };
        let h = Health { hp: 100 };
        if i % 2 == 0 {
            world.spawn((p, Velocity { x: 2, y: 1 }, h));
        } else {
            world.spawn((p, h));
        }
    }
    let mut schedule = Schedule::default();
    schedule.set_executor(SingleThreadedExecutor::default());
    schedule.add_systems((movement, damage).chain());
    schedule.initialize(&mut world).expect("valid ECS schedule");
    let start = Instant::now();
    for _ in 0..ticks {
        schedule.run(black_box(&mut world));
    }
    let elapsed = start.elapsed();
    let mut query = world.query::<(&Position, &Health)>();
    let sum = query.iter(&world).map(|(p, h)| p.x + p.y + h.hp).sum();
    (sum, elapsed)
}

#[derive(Default)]
struct MovingTable {
    positions: Vec<Position>,
    velocities: Vec<Velocity>,
    health: Vec<Health>,
}

#[derive(Default)]
struct StillTable {
    positions: Vec<Position>,
    health: Vec<Health>,
}

fn columns(n: i64, ticks: i64) -> (i64, Duration) {
    let mut moving = MovingTable::default();
    let mut still = StillTable::default();
    for i in 0..n {
        let p = Position { x: i, y: 2 * i };
        let h = Health { hp: 100 };
        if i % 2 == 0 {
            moving.positions.push(p);
            moving.velocities.push(Velocity { x: 2, y: 1 });
            moving.health.push(h);
        } else {
            still.positions.push(p);
            still.health.push(h);
        }
    }
    let start = Instant::now();
    for _ in 0..ticks {
        let moving = black_box(&mut moving);
        let still = black_box(&mut still);
        for (p, v) in moving.positions.iter_mut().zip(&moving.velocities) {
            p.x += v.x;
            p.y += v.y;
        }
        for h in moving.health.iter_mut().chain(&mut still.health) {
            h.hp -= 1;
        }
    }
    let elapsed = start.elapsed();
    let sum = moving
        .positions
        .iter()
        .zip(&moving.health)
        .chain(still.positions.iter().zip(&still.health))
        .map(|(p, h)| p.x + p.y + h.hp)
        .sum();
    (sum, elapsed)
}

fn expected(n: i64, ticks: i64) -> i64 {
    3 * n * (n - 1) / 2 + 100 * n - ticks * n + 3 * ticks * ((n + 1) / 2)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() > 2 {
        return Err("usage: weft-ecs-compare [entities [ticks]]".into());
    }
    let n = args.first().map_or(Ok(64_i64), |s| s.parse())?;
    let ticks = args.get(1).map_or(Ok(10_i64), |s| s.parse())?;
    if !(0..=1_000_000).contains(&n) || !(0..=1_000_000).contains(&ticks) {
        return Err("entities and ticks must each be in 0..=1000000".into());
    }
    let want = expected(n, ticks);
    for (name, (sum, time)) in [
        ("rust-columns", columns(n, ticks)),
        ("bevy", bevy(n, ticks)),
    ] {
        if sum != want {
            return Err(format!("{name}: checksum {sum}, expected {want}").into());
        }
        println!(
            "{name}: entities={n} ticks={ticks} checksum={sum} elapsed_us={}",
            time.as_micros()
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_controls_match_the_workload() {
        for n in [0, 1, 2, 5, 64] {
            for ticks in [0, 1, 10] {
                assert_eq!(columns(n, ticks).0, expected(n, ticks));
                assert_eq!(bevy(n, ticks).0, expected(n, ticks));
            }
        }
        assert_eq!(expected(64, 10), 12768);
    }
}
