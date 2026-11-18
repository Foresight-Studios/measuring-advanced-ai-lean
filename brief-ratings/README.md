# Ratings: Can Advanced AI Systems Be Told Apart by Measurement?

These are the ratings behind The Uncontainability Project's research brief *Can Advanced AI Systems Be Told Apart by Measurement?* (November 2026). We wrote the brief to inform our public comment on the U.S. Treasury's proposed rule 31 CFR Part 851 (docket TREAS-DO-2026-0595).

The brief rates 55 ways of classifying or ranking AI systems on six tests. This folder gives every rating with its reason and a source link, so that any rating can be checked.

- `ratings.csv`: one row per approach. The row numbers match the brief's annex table.
- `ratings.json`: the same data in JSON.

## The six tests

Each test is rated Yes, Partly or No.

| Column | Test | Question |
| --- | --- | --- |
| T1 | Scale | Can a rule draw a line on it, and move the line later? Yes: an ordered or continuous scale. Partly: a few ordered levels. No: a single in-or-out category. |
| T2 | Third-party measurable | Could someone other than the developer measure where a system stands without the developer's help? |
| T3 | Specified measurement | Does the source specify the tasks or quantity measured, the procedure or sample size, and the error or uncertainty? Yes: all three. Partly: some of them. |
| T4 | Robust to post-training | Does it still track capability when the gain comes from post-training, inference-time compute or scaffolding? |
| T5 | Harm evidence | Has a system's position on the measure been shown to predict realized harm, or a harm proxy validated against it? Partly: the measure's own values correlate with a harm evaluation that has not itself been validated against harm. |
| T6 | Binding use | Yes: used in an enacted law or binding rule. Partly: used in a voluntary commitment or company policy. No: only proposed. |

## Notes on the ratings

- **Sources and date.** Ratings are as of 18 November 2026. Each one was checked against the approach's primary source.
- **Secondary sources.** `secondary_source = yes` marks the one rating that rests on secondary sources: row 41, China's AI Safety Governance Framework 2.0.
- **Who wrote them.** The reasons were drafted by AI research assistants working from the sources, then reviewed and edited by the project. Some keep a first-person research note.

## Corrections

If you think a rating is wrong, please tell us through [agiuncontainability.org](https://agiuncontainability.org) or open an issue in this repository.
