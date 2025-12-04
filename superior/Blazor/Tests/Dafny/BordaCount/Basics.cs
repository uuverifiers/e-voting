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

using Dafny;
using E_Voting;
using E_Voting.Transfer;
using Google.Protobuf.WellKnownTypes;
using Microsoft.AspNetCore.Mvc;
using System.Text.Json;
using System.Web;

namespace Core.BordaCount
{
    public class Basics
    {
        private Dictionary<string, int>? GetResult(List<Vote> votes, List<Candidate> candidates)
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
                "5"
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
        public void Permutations()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes1 =
            [
                new Vote(1, "[5,4,3,2,1]", 0),
                new Vote(2, "[1,2,3,4,5]", 0),
                new Vote(3, "[2,3,4,5,1]", 0)
            ];

            List<Vote> votes2 =
            [
                new Vote(2, "[1,2,3,4,5]", 0),
                new Vote(3, "[2,3,4,5,1]", 0),
                new Vote(1, "[5,4,3,2,1]", 0)
            ];

            List<Vote> votes3 =
            [
                new Vote(2, "[1,2,3,4,5]", 0),
                new Vote(1, "[5,4,3,2,1]", 0),
                new Vote(3, "[2,3,4,5,1]", 0)
            ];

            var expected = new Dictionary<string, int>
            {
                { "1", 7 },
                { "2", 11 },
                { "3", 10 },
                { "4", 9 },
                { "5", 8 }
            };

            Assert.Equal(expected, GetResult(votes1, candidates));
            Assert.Equal(expected, GetResult(votes2, candidates));
            Assert.Equal(expected, GetResult(votes3, candidates));
        }

        [Fact]
        public void PermutationsLarge()
        {
            int candidatesNumber = 10;
            int votesNumber = 100;
            Random random = new Random(1234);

            var expected = JsonSerializer.Deserialize<Dictionary<string, int>>
            ("{\"0\":513,\"1\":545,\"2\":569,\"3\":607,\"4\":533,\"5\":539,\"6\":526,\"7\":610,\"8\":567,\"9\":491}");

            List<Candidate> candidates = new List<Candidate>();
            for (int i = 0; i < candidatesNumber; i++)
            {
                candidates.Add(new Candidate(i, i.ToString(), 0));
            }

            List<Vote> votes = new List<Vote>();
            for (int i = 0; i < votesNumber; i++)
            {
                List<long> pool = new List<long>();
                foreach(Candidate candidate in candidates)
                {
                    pool.Add(candidate.ID);
                }

                string value = "[";
                foreach (Candidate candidate in candidates)
                {
                    int index = random.Next(0, pool.Count);
                    value += pool[index] + ",";
                    pool.RemoveAt(index);
                }
                value = value.Remove(value.Length - 1);
                value += "]";

                votes.Add(new Vote(votes.Count, value, 0));
            }

            int loops = 100;
            for (int i = 0; i < loops; i++)
            {
                Help.Shuffle(votes);
                Assert.Equal(expected, GetResult(votes, candidates));
            }
        }

        [Fact]
        public void CharAsKey()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
                new Vote(2, "[5,4,A,2,1]", 0),
                new Vote(3, "[2,3,4,5,1]", 0)
            ];

            Exception ex = Assert.Throws<FormatException>(() => GetResult(votes, candidates));
            Assert.Equal("The value could not be parsed.", ex.Message);
        }

        [Fact]
        public void InvalidVote()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
                new Vote(2, "[5,4,3,2,1]", 0),
                new Vote(3, "[2,3,4,5,6]", 0)
            ];

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
        }

        [Fact]
        public void DuplicateVote()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,5,5]", 0),
                new Vote(2, "[5,4,3,2,1]", 0),
                new Vote(3, "[2,3,4,5,6]", 0)
            ];

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
        }

        [Fact]
        public void ShorterVote()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
                new Vote(2, "[5,4,2,1]", 0),
                new Vote(3, "[2,3,4,5,1]", 0)
            ];

            var expected = new Dictionary<string, int>
            {
                { "1", 7 },
                { "2", 11 },
                { "3", 7 },
                { "4", 8 },
                { "5", 7 }
            };

            Assert.Equal(expected, GetResult(votes, candidates));
        }

        [Fact]
        public void OneVote()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(2, "[1,2,3,4,5]", 0),
            ];

            var expected = new Dictionary<string, int>
            {
                { "1", 5 },
                { "2", 4 },
                { "3", 3 },
                { "4", 2 },
                { "5", 1 }
            };

            Assert.Equal(expected, GetResult(votes, candidates));
        }

        [Fact]
        public void NoVotes()
        {
            // Info: Elections without votes get deleted instead of evaluated

            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0)
            ];

            List<Vote> votes = new();

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
        }

        [Fact]
        public void NoCandidates()
        {
            // Info: Elections without candidates get rejected by server logic

            List<Candidate> candidates = new();

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
            ];

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
        }

        [Fact]
        public void NoInput()
        {
            List<Candidate> candidates = new();
            List<Vote> votes = new();

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
        }

        [Fact]
        public void AllwaysFirst()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
                new Vote(2, "[1,2,4,3,5]", 0),
                new Vote(3, "[1,5,3,4,2]", 0),
                new Vote(4, "[1,2,3,4,5]", 0),
                new Vote(5, "[1,2,5,4,3]", 0),
            ];

            string winner = GetResult(votes, candidates)!.Aggregate((l, r) => l.Value > r.Value ? l : r).Key;
            string expected = "1";

            Assert.Equal(winner, expected);
        }

        [Fact]
        public void EmptyVotes()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
                new Vote(2, "[1,2,3,4,5]", 0),
                new Vote(3, "[]", 0),
                new Vote(4, "[]", 0),
                new Vote(5, "[1,2,3,4,5]", 0)
            ];

            var expected = new Dictionary<string, int>
            {
                { "1", 15 },
                { "2", 12 },
                { "3", 9 },
                { "4", 6 },
                { "5", 3 }
            };

            Assert.Equal(expected, GetResult(votes, candidates));
        }

        [Fact]
        public void SuperShortVotes()
        {
            List<Candidate> candidates =
            [
                new Candidate(1, "A", 0),
                new Candidate(2, "B", 0),
                new Candidate(3, "C", 0),
                new Candidate(4, "D", 0),
                new Candidate(5, "E", 0),
            ];

            List<Vote> votes =
            [
                new Vote(1, "[1,2,3,4,5]", 0),
                new Vote(2, "[1,2,3,4,5]", 0),
                new Vote(3, "[1]", 0),
                new Vote(4, "[1]", 0),
                new Vote(5, "[1,2,3,4,5]", 0)
            ];

            var expected = new Dictionary<string, int>
            {
                { "1", 17 },
                { "2", 12 },
                { "3", 9 },
                { "4", 6 },
                { "5", 3 }
            };

            Assert.Equal(expected, GetResult(votes, candidates));
        }
    }
}
