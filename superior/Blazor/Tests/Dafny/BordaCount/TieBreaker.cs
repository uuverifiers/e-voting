// Formally verified E-Voting using Dafny
// Copyright (C) 2025 Authors Superior Group
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU Affero General Public License for more details.
// You should have received a copy of the GNU Affero General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

using E_Voting;
using E_Voting.Transfer;
using System.Text.Json;

namespace Core.BordaCount
{
    public class TieBreaker
    {
        private Dictionary<string, int>? GetResult(List<Vote> votes, List<Candidate> candidates, int tieBreaker)
        {
            Election election = new Election
            (
                0,
                "name",
                "description",
                DateTime.UtcNow.AddDays(7),
                false,
                false,
                1,
                Config.EmptyResult,
                "admin_token",
                "some@mail.de",
                tieBreaker.ToString()
            );
            foreach(Candidate element in candidates)
            {
                election.AddCandidate(element);
            }
            foreach (Vote element in votes)
            {
                election.AddVote(element);
            }

            string json_result = DafnyWrapper.GetResultForTests(election);
            return JsonSerializer.Deserialize<Dictionary<string, int>>(json_result);
        }

        [Fact]
        public void TieGetsResolved()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0)
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3]", 0),
                new Vote(2, "[2,1,3]", 0),
                new Vote(3, "[2,1,3]", 0),
            ];

            var result = GetResult(votes, candidates, 10);
            var top2 = result!.OrderByDescending(x => x.Value).Take(2).ToList();
            Assert.NotEqual(top2[0].Value, top2[1].Value);
        }

        [Fact]
        public void NoTieBreaker()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0)
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2]", 0),
                new Vote(2, "[2,1]", 0),
            ];

            var result = GetResult(votes, candidates, 0);
            var top2 = result!.OrderByDescending(x => x.Value).Take(2).ToList();
            Assert.Equal(top2[0].Value, top2[1].Value);
        }

        [Fact]
        public void AllEqualWithTieBreaker()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0)
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3]", 0),
                new Vote(2, "[2,3,1]", 0),
                new Vote(3, "[3,1,2]", 0),
            ];

            var result = GetResult(votes, candidates, 10)!.ToList();
            Assert.Equal(result[0].Value, result[1].Value);
            Assert.Equal(result[1].Value, result[2].Value);
        }
    }
}
