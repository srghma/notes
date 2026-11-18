import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "Kraken P3 / VCGen Branch Tree & Timeline",
  description:
    "Chronological branch DAG and Lean file group explorer for kraken.",
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en" className="dark h-dvh overflow-hidden antialiased">
      <body className="h-dvh w-screen overflow-hidden flex flex-col bg-zinc-950 text-zinc-100">
        {children}
      </body>
    </html>
  );
}
