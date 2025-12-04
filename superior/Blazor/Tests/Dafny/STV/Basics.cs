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
using System.Text.Json;

namespace Core.STV
{
    public class Basics
    {
        private List<int>? GetResult(List<Vote> votes, List<Candidate> candidates)
        {
            Election election = new Election
            (
                0,
                "name",
                "description",
                DateTime.UtcNow.AddDays(7),
                false,
                false,
                2,
                Config.EmptyResult,
                "admin_token",
                "some@mail.de",
                "3"
            );
            foreach (Candidate element in candidates)
            {
                election.AddCandidate(element);
            }
            foreach (Vote element in votes)
            {
                election.AddVote(element);
            }

            string json_result = DafnyWrapper.GetResultForTests(election);
            return JsonSerializer.Deserialize<List<int>>(json_result);
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

            List<int> expected = [1, 2, 5];

            Assert.Equal(expected, GetResult(votes1, candidates));
            Assert.Equal(expected, GetResult(votes2, candidates));
            Assert.Equal(expected, GetResult(votes3, candidates));
        }

        [Fact]
        public void PartialVote()
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
                new Vote(1, "[1,2,3,4]", 0),
                new Vote(2, "[5,4,3,2]", 0),
                new Vote(3, "[2,3,5]", 0)
            ];

            List<int> expected = [1, 2, 5];

            Assert.Equal(expected, GetResult(votes, candidates));
        }

        [Fact]
        public void NormalPlusEmptyVotes()
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
                new Vote(2, "[]", 0),
                new Vote(3, "[]", 0),
                new Vote(4, "[5,4,3,2,1]", 0),
                new Vote(5, "[2,3,5,1,4]", 0)
            ];

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
        }

        [Fact]
        public void JustEmptyVotes()
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
                new Vote(1, "[]", 0),
                new Vote(2, "[]", 0),
                new Vote(3, "[]", 0),
            ];

            Exception ex = Assert.Throws<HaltException>(() => GetResult(votes, candidates));
            Assert.Contains("Votes or Candidates don't match pre-conditions!", ex.Message);
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
                new Vote(1, "[1,2,3,4,5]", 0),
            ];

            List<int> expected = [1, 4, 5];

            Assert.Equal(expected, GetResult(votes, candidates));
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
    }
}
