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

using Microsoft.AspNetCore.Components;
using Microsoft.AspNetCore.Components.Web;
using Microsoft.AspNetCore.HttpOverrides;

namespace E_Voting
{
    public class Program
    {
        public static void Main(string[] args)
        {
            // load config
            Config.Load();

            // start evaluation thread
            Thread evaluationThread = new Thread(DafnyWrapper.Check);
            evaluationThread.IsBackground = true;
            evaluationThread.Start();

            // start cleaner thread
            Thread cleanerThread = new Thread(Cleaner.Check);
            cleanerThread.IsBackground = true;
            cleanerThread.Start();

            // start reminder thread
            Thread reminderThread = new Thread(Reminder.Check);
            reminderThread.IsBackground = true;
            reminderThread.Start();

            var builder = WebApplication.CreateBuilder(args);

            // Add services to the container.
            builder.Services.AddRazorPages();
            builder.Services.AddServerSideBlazor()
            .AddHubOptions(options =>
            {
                options.ClientTimeoutInterval = TimeSpan.FromSeconds(90); // default 30
                options.KeepAliveInterval = TimeSpan.FromSeconds(45);     // default 15
            });


            var app = builder.Build();

            app.UsePathBase("/superior");

            app.UseForwardedHeaders(new ForwardedHeadersOptions
            {
                ForwardedHeaders = ForwardedHeaders.XForwardedFor | ForwardedHeaders.XForwardedProto
            });

            // Configure the HTTP request pipeline.
            if (!app.Environment.IsDevelopment())
            {
                app.UseExceptionHandler("/Error");
            }

            // Enable static files with unknown MIME types
            app.UseStaticFiles(new StaticFileOptions
            {
                ServeUnknownFileTypes = true
            });

            app.UseAntiforgery();

            app.UseRouting();

            app.MapBlazorHub();
            app.MapFallbackToPage("/_Host");

            app.Run();
        }
    }
}